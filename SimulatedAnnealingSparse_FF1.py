# ==============================================================
#  SASparseDelayFF.py  
#  非アイランドスタイルeFPGA向け SAベース配置・配線 + 遅延最適化スクリプト
#  - Phase-1: 配置・配線（必須）
#  - Phase-2: 遅延最適化（任意、DELAY=True のとき実行）
#  - SECTION0: 設定・共通インポート
#  - SECTION1: Netlist / XML 解析
#  - SECTION2: Phase-1 SA（配線可能性判定）
#  - SECTION3: Phase-2 SA（遅延最適化）
#  - SECTION4: Bind/Connect 生成
#  - SECTION5: クリティカルパス解析ユーティリティ
#  - SECTION6: トップレベルドライバ（Phase1/Phase2 を呼ぶ）
# ==============================================================


# ==============================================================
#  SECTION0: 設定・共通インポート
# ==============================================================
import networkx as nx
import sys, re, math, time, random, xml.etree.ElementTree as ET
from collections import defaultdict, deque

# True: Phase-2 まで実行（mapped.v 必須）
# False: Phase-2 はスキップ（mapped.v なしでもOK）
DELAY = True


# ==============================================================
#  SECTION1: Netlist / XML 解析 
# ==============================================================
# ====== Netlist ======
class PAE:
    def __init__(self, name, inputs, outputs):
        self.name = name
        self.inputs = inputs
        self.outputs = outputs

def read_netlist(file_path, nPIs):
    paes = []
    const_signals = set()
    external_inputs = {}
    external_outputs = {}
    output_to_pae_map = {}   # ★raw: out_sig or FF.Q -> [(dst_pae, in_port)]
    defined_inputs = set()
    defined_outputs = set()
    ff_list = []             # ★追加: [(ff_name, D, Q)]

    with open(file_path, 'r', encoding='utf-8') as f:
        for line in f:
            parts = line.strip().split()
            if not parts: continue
            if parts[0] == "inputs":
                defined_inputs = set(parts[1:]); continue
            if parts[0] == "outputs":
                defined_outputs = set(parts[1:]); continue
            if parts[0] == "const":
                if len(parts) > 1: const_signals.add(parts[1]); continue
            if parts[0] == "ff":
                if len(parts) >= 4:
                    ff_list.append((parts[1], parts[2], parts[3]))  # (name, D, Q)
                continue
            if parts[0] == "pae":
                name = parts[1]
                in_signals  = [s if s not in const_signals else "nc" for s in parts[2:6]]
                out_signals = [s if s not in const_signals else "nc" for s in parts[6:9]]
                inputs  = {i:s for i,s in enumerate(in_signals)  if s!="nc"}
                outputs = {i:s for i,s in enumerate(out_signals) if s!="nc"}

                for port, inp in inputs.items():
                    if inp in defined_inputs:
                        external_inputs.setdefault(inp, []).append((name, port))
                for port, out in outputs.items():
                    if out in defined_outputs:
                        external_outputs[(name, port)] = out

                paes.append(PAE(name, inputs, outputs))

    # --- raw: PAE出力 -> PAE入力
    for p in paes:
        for _, out_sig in p.outputs.items():
            for d in paes:
                for in_port, inp in d.inputs.items():
                    if inp == out_sig:
                        output_to_pae_map.setdefault(out_sig, []).append((d.name, in_port))

    # --- ★raw: FF.Q -> PAE入力（viaFF検出のためQ名でキー化）
    ff_q_set = {q for (_ff, _d, q) in ff_list}
    for d in paes:
        for in_port, inp in d.inputs.items():
            if inp in ff_q_set:
                output_to_pae_map.setdefault(inp, []).append((d.name, in_port))

    # --- ★FF.Q が外部出力なら、D を出す PAE出力を外部出力扱いへ昇格
    outname_set = set(defined_outputs)
    q_to_d = {q: d for (_ff, d, q) in ff_list}
    for q_sig, d_sig in q_to_d.items():
        if q_sig in outname_set:
            for p in paes:
                for out_port, out_sig in p.outputs.items():
                    if out_sig == d_sig:
                        external_outputs[(p.name, out_port)] = q_sig

    # --- ★評価用: D≡Q 同一視のマップ
    class DSU:
        def __init__(self): self.p={}
        def find(self,x):
            if x in (None,"nc"): return x
            if x not in self.p: self.p[x]=x
            if self.p[x]!=x: self.p[x]=self.find(self.p[x])
            return self.p[x]
        def union(self,a,b):
            if a in (None,"nc") or b in (None,"nc"): return
            ra,rb=self.find(a),self.find(b)
            if ra!=rb: self.p[rb]=ra

    dsu = DSU()
    for _ff, d, q in ff_list:
        dsu.union(d,q)

    def norm(sig): return dsu.find(sig)

    norm_output_to_pae_map = {}
    for sig, sinks in output_to_pae_map.items():
        k = norm(sig)
        norm_output_to_pae_map.setdefault(k, []).extend(sinks)

    return (
        paes,
        external_inputs,
        external_outputs,
        output_to_pae_map,      # raw（viaFF判定用）
        ff_list,                # ★
        norm_output_to_pae_map  # SA評価用
    )

# ====== XML ======
def parse_fpga_connection_all(xml_file):
    tree = ET.parse(xml_file)
    root = tree.getroot()

    # ---- 集約したい情報（すべて作る。必要なものだけ返す） ----
    imux_map = {}            # imux名 -> inputs配列（信号名）
    omux_map = {}            # omux名 -> dsts配列（到達ノード名）
    ff_map = {}              # ffnode名 -> dsts配列（到達ノード名）
    pae_to_ff_map = {}       # "pae{out}_{pid}_{lane}" -> ffnode名
    skipomux_count = {}      # lane番号 -> そのレーンのOMUX個数
    pae_output_signals = {}  # "pae{out}_{pid}_{lane}" -> dsts配列
    target_names = []        # 物理PAEセル名 "pae{pid}_{lane}"
    lanes = set()            # 使っているレーン集合

    # fanin算出用（キー=ノード名, 値=inputsの配列）
    imux_inputs = {}
    omux_inputs = {}

    # PrimalInput（外部入力）個数
    nPIs = 0

    # -------- 1st pass: 型で数えたいもの --------
    for el in root.findall(".//element"):
        typ = (el.findtext("type") or "").strip()
        if typ == "PrimalInput":
            nPIs += 1

    # -------- 2nd pass: 各種マップ構築 --------
    for el in root.findall(".//element"):
        name = (el.findtext("name") or "").strip()
        typ  = (el.findtext("type") or "").strip().upper()

        # --- IMUX/OMUXのinputs（fanin計算用） ---
        if typ in ("IMUX", "OMUX"):
            ins = [ (it.text or "").strip() for it in el.findall("inputs/item") ]
            if typ == "IMUX":
                imux_inputs[name] = ins
            else:
                omux_inputs[name] = ins

        # --- IMUX: 入力一覧（互換のため保持） ---
        if name.startswith("imux"):
            imux_map[name] = [ (it.text or "").strip() for it in el.findall("inputs/item") ]

        # --- OMUX: 出力先/スキップ数/inputs（fanin） ---
        if name.startswith("omux"):
            dsts = [ (it.text or "").strip() for it in el.findall("dsts/item") ]
            omux_map[name] = dsts

            m = re.match(r"omux\d+_(\d+)", name)
            if m:
                lane = int(m.group(1))
                skipomux_count[lane] = skipomux_count.get(lane, 0) + 1

        # --- FFノード: 到達先と、PAE出力→FF の逆引き ---
        if name.startswith("ffnode") or typ in ("FFNODE", "FLIPFLOPNODE"):
            ff_dsts = [ (it.text or "").strip() for it in el.findall("dsts/item") ]
            ff_map[name] = ff_dsts
            inputs = el.find("inputs")
            if inputs is not None:
                for it in inputs.findall("item"):
                    src_pae = (it.text or "").strip()  # e.g., "pae0_0_0"
                    if src_pae:
                        pae_to_ff_map[src_pae] = name

    # --- PAEセル（物理セルと出力ノード） ---
    for el in root.findall(".//element"):
        name = (el.findtext("name") or "").strip()
        if not name:
            continue

        # 物理PAEセル: "pae{pid}_{lane}"
        if re.match(r"pae\d+_\d+$", name):
            target_names.append(name)
            try:
                lanes.add(int(name.split("_")[1]))
            except Exception:
                pass

        # PAEの各出力ノード: "pae{out}_{pid}_{lane}"
        elif re.match(r"pae\d+_\d+_\d+$", name):
            pae_output_signals[name] = [ (it.text or "").strip() for it in el.findall("dsts/item") ]

    # ---- fanin 辞書に変換 ----
    imux_fanin = {k: len(v) for k, v in imux_inputs.items()}
    omux_fanin = {k: len(v) for k, v in omux_inputs.items()}

    return (imux_map, omux_map, ff_map, pae_to_ff_map,
            skipomux_count, target_names, pae_output_signals,
            nPIs, imux_fanin, omux_fanin)


# ==============================================================
#  SECTION2: Phase-1 SA（配線可能性判定）
# ==============================================================
# ====== 初期配置生成 ======
def generate_initial_placement(paes, target_names, output_to_pae_map, ng_placement=None):
    logic_names = [p.name for p in paes]
    placement = {}
    used = set()
    for logic in logic_names:
        candidates = []
        for cell in target_names:
            if cell in used: continue
            lane = int(cell.split("_")[1])
            score = 0
            for sig, dsts in output_to_pae_map.items():
                for dst_logic, _ in dsts:
                    if dst_logic != logic: continue
                    for p in paes:
                        if sig in p.outputs.values():
                            src_logic = p.name
                            if src_logic in placement:
                                src_lane = int(placement[src_logic].split("_")[1])
                                if lane == src_lane + 1: score += 15
            candidates.append((score, cell))
        candidates.sort(reverse=True)
        sel = candidates[0][1] if candidates else random.choice([t for t in target_names if t not in used])
        placement[logic] = sel; used.add(sel)
    return [placement[p.name] for p in paes]

# ===== 最大マッチングによる外部入力割り当て ======
def assign_inputs_with_maximum_matching(PI_map):
    G = nx.Graph()
    for signal, candidates in PI_map.items():
        for pi in candidates:
            G.add_edge(f"sig::{signal}", f"pi::{pi}")
    matching = nx.algorithms.matching.max_weight_matching(G, maxcardinality=True)

    PI_assignments = {}
    for u, v in matching:
        if u.startswith("sig::"):
            signal = u[5:]
            pi = v[4:]
        elif v.startswith("sig::"):
            signal = v[5:]
            pi = u[4:]
        else:
            continue
        PI_assignments[signal] = pi
    return PI_assignments

# ====== 配線可能性判定 ======
def evaluate_routability(pae_placement_map, paes, external_inputs,
                         imux_map, omux_map, ff_map, pae_to_ff_map,
                         pae_output_signals, norm_output_to_pae_map, skipomux_count):
    total_penalty = 0
    used_skip_omux = {}  # {src_lane: set(signal)}
    PI_map = {}  # 外部入力の配線可能性チェック

    # 外部入力の配線可能性チェック
    for signal, destinations in external_inputs.items():
        PI_candidates = None
        imux_missing = False

        for pae_name, input_port in destinations:
            if pae_name not in pae_placement_map:
                continue
            dst_pae = pae_placement_map[pae_name]
            dst_id = int(dst_pae.split("_")[0][3:])
            dst_lane = int(dst_pae.split("_")[1])
            imux_name = f"imux{input_port}_{dst_id}_{dst_lane}"

            if imux_name not in imux_map:
                imux_missing = True
                break

            PI_sources = {src for src in imux_map[imux_name] if src.startswith("EFPGA_I[")}
            if PI_candidates is None:
                PI_candidates = PI_sources
            else:
                PI_candidates &= PI_sources

        if imux_missing:
            total_penalty += 100
        elif not PI_candidates:
            total_penalty += 100
        else:
            PI_map[signal] = PI_candidates

    # --- PI 最大マッチング ---
    PI_assignments = assign_inputs_with_maximum_matching(PI_map)
    unmatched_signals = len(PI_map) - len(PI_assignments)
    total_penalty += unmatched_signals * 100

    # --- PAE間配線 ---
    for pae in paes:
        src_pae = pae_placement_map[pae.name]
        src_lane = int(src_pae.split("_")[1])
        omux_candidates = [f"omux{i}_{src_lane}" for i in range(skipomux_count.get(src_lane, 0))]

        for output_port, output_signal in pae.outputs.items():
            if output_signal not in norm_output_to_pae_map:
                continue
            for dst_pae_name, input_port in norm_output_to_pae_map[output_signal]:
                dst_pae = pae_placement_map[dst_pae_name]
                dst_id = int(dst_pae.split("_")[0][3:])
                dst_lane = int(dst_pae.split("_")[1])

                if dst_lane == src_lane + 1:
                    src_id = int(src_pae.split("_")[0][3:])
                    src_lane = int(src_pae.split("_")[1])
                    src_output = f"pae{output_port}_{src_id}_{src_lane}"
                    ffnode_name = pae_to_ff_map.get(src_output)
                    imux_key = f"imux{input_port}_{dst_id}_{dst_lane}"

                    if ffnode_name in ff_map:
                        if imux_key not in ff_map[ffnode_name]:
                            total_penalty += 100
                    else:
                        total_penalty += 100
                else:
                    if not omux_candidates:
                        total_penalty += 100
                        continue
                    omux = omux_candidates[0]
                    if omux in omux_map:
                        imux_key = f"imux{input_port}_{dst_id}_{dst_lane}"
                        if imux_key in omux_map[omux]:
                            if src_lane not in used_skip_omux:
                                used_skip_omux[src_lane] = set()
                            used_skip_omux[src_lane].add(output_signal)
                        else:
                            total_penalty += 100
                    else:
                        total_penalty += 100

    for lane, signals in used_skip_omux.items():
        total_usage = len(signals)
        limit = skipomux_count.get(lane, 0)
        overuse = max(0, total_usage - limit)
        total_penalty += overuse * 100

    ng_placement = set()
    return total_penalty, PI_assignments, ng_placement

# ====== Phase-1 Simulated Annealing ======
def simulated_annealing_phase1(paes, external_inputs, target_names, imux_map, omux_map, ff_map,
                        pae_to_ff_map, pae_output_signals, skipomux_count, norm_output_to_pae_map,
                        max_iters=500000, initial_temp=100):
    # 初期配置
    ng_placement = set()
    placement = generate_initial_placement(paes, target_names, norm_output_to_pae_map, ng_placement)

    # 論理要素と物理要素の割り当て
    pae_placement_map = {paes[i].name: placement[i] for i in range(len(paes))}

    # 初期評価
    best_cost, best_pi, ng_placement = evaluate_routability(
        pae_placement_map, paes, external_inputs, imux_map, omux_map, ff_map,
        pae_to_ff_map, pae_output_signals, norm_output_to_pae_map, skipomux_count)
    best_placement = placement[:]

    min_temp = 1.0
    use_swap_only = (len(target_names) == len(paes))

    for iteration in range(max_iters):
        progress = iteration / (max_iters - 1)

        # パラメータ：好みに応じて調整
        m = 0.50      # どの進捗から温度を落とし始めるか（0.7=終盤）
        k = 12.0      # カーブの急峻さ（大きいほど急激に）

        # Logisticシグモイドで滑らかに「前半ゆっくり・後半急激」
        L = 1.0 / (1.0 + math.exp(-k * (progress - m)))
        temp = min_temp + (initial_temp - min_temp) * (1.0 - L)

        new_placement = best_placement[:]

        if use_swap_only:
            i, j = random.sample(range(len(paes)), 2)
            new_placement[i], new_placement[j] = new_placement[j], new_placement[i]
        else:
            i = random.randint(0, len(paes) - 1)
            used_cells = set(new_placement)
            available_cells = [cell for cell in target_names if cell not in used_cells or cell == new_placement[i]]
            if new_placement[i] in available_cells:
                available_cells.remove(new_placement[i])
            if not available_cells:
                continue
            new_cell = random.choice(available_cells)
            new_placement[i] = new_cell

        new_pae_placement_map = {paes[k].name: new_placement[k] for k in range(len(paes))}
        new_cost, new_pi, ng_placement = evaluate_routability(
            new_pae_placement_map, paes, external_inputs, imux_map, omux_map, ff_map,
            pae_to_ff_map, pae_output_signals, norm_output_to_pae_map, skipomux_count)

        delta = new_cost - best_cost
        if delta < 0 or random.random() < math.exp(-delta / temp):
            best_placement = new_placement[:]
            best_cost = new_cost
            best_pi = new_pi

        if best_cost == 0:
            print(f"[SA_ITER_PHASE1] {iteration+1}")
            break

    final_map = {paes[i].name: best_placement[i] for i in range(len(paes))}
    final_penalty, final_pi, ng_placement = evaluate_routability(
        final_map, paes, external_inputs, imux_map, omux_map, ff_map,
        pae_to_ff_map, pae_output_signals, norm_output_to_pae_map, skipomux_count)

    if final_penalty > 0:
        print("[ERROR] 配置が完了しませんでした（ペナルティ > 0）")
        print("[PnR_RESULT] Failed")
        sys.exit(1)

    return final_map, final_pi


# ==============================================================
#  SECTION3: Phase-2 SA（遅延最適化）
# ==============================================================
# ====== N入力MUX遅延値テーブル ======
MUX_DELAY_MAX_NS = {
    2:0.13,4:0.18,8:0.20,16:0.27,18:0.30,24:0.30,27:0.32,28:0.33,30:0.34,
    32:0.34,33:0.34,36:0.31,37:0.35,40:0.31,35:0.32,43:0.38,45:0.38,46:0.38,48:0.37,49:0.36, 51:0.37, 52:0.37, 54:0.38, 57:0.39, 58:0.4, 60:0.4,
    64:0.34,70:0.4,74:0.35,82:0.36,86:0.34,88:0.35,90:0.33,94:0.37,102:0.36,106:0.35,114:0.33,118:0.34,124:0.3,128:0.29,
    130:0.32,136:0.34,184:0.31,196:0.33,
    206:0.32,208:0.36,215:0.36,222:0.37,
    238:0.33,254:0.28,256:0.28,260:0.32,288:0.31,
    302:0.35,318:0.34,320:0.31,350:0.35,
}
PIN_IN_TO_IDX  = {"I_a":0, "I_b":1, "I_c":2, "I_d":3}
PIN_OUT_TO_IDX = {"O_a":0, "O_b":1, "O_c":2}

CELL_RE = re.compile(r'\\cell\s*#\(\s*\.MODE\((8\'h[0-9a-fA-F]+)\)\s*\)\s*([_A-Za-z0-9$]+)\s*\(', re.S)

# ====== インスタンス名正規化 ======
def norm(s): return None if s is None else s.lstrip("\\").strip()

# ===== PAEアーク遅延値テーブル ======
PAE_ARCS = {
    "01":[("I_a","O_a",0.18),("I_a","O_b",0.32),("I_a","O_c",0.47),
          ("I_b","O_a",0.27),("I_b","O_b",0.41),("I_b","O_c",0.56),
          ("I_c","O_b",0.33),("I_c","O_c",0.48),("I_d","O_c",0.23)],
    "00":[("I_a","O_a",0.19),
          ("I_b","O_a",0.44),("I_b","O_b",0.26),("I_b","O_c",0.40),
          ("I_c","O_a",0.48),("I_c","O_b",0.29),("I_c","O_c",0.44),
          ("I_d","O_c",0.23)],
    "11":[("I_a","O_a",0.18),("I_a","O_b",0.33),
          ("I_b","O_a",0.27),("I_b","O_b",0.41),
          ("I_c","O_b",0.44),("I_c","O_c",0.24),
          ("I_d","O_b",0.43),("I_d","O_c",0.23)],
    "10":[("I_a","O_a",0.19),
          ("I_b","O_a",0.45),("I_b","O_b",0.26),
          ("I_c","O_a",0.65),("I_c","O_b",0.45),("I_c","O_c",0.26),
          ("I_d","O_a",0.62),("I_d","O_b",0.43),("I_d","O_c",0.24)],
}

# ====== mapped.v の名前整形 ======
def _norm_inst_name_basic(s: str) -> str:
    if s is None: return ""
    s = s.strip()
    if s.startswith("\\"):
        s = s[1:]
    s = re.sub(r'\[[^\]]+\]$', '', s)
    s = re.sub(r'\$.*$', '', s)
    if '.' in s:
        s = s.split('.')[-1]
    return s

# ====== mapped.v → MODE[7:6] 抽出 ======
def parse_logic_mode_from_mapped_v(mapped_v_path, bind_vars_info=None):
    """
    mapped.vから各PAEインスタンスのMODE[7:6]を抽出する。
    
    引数:
        mapped_v_path: mapped.vファイルのパス
        bind_vars_info: オプション。bind_vars_infoが提供された場合、GEN_{番号}_パターンの
                       PAEインスタンスを検出してデフォルトMODE（8'h00 → "00"）を割り当てる。
    
    戻り値: Dict[str, str]
        - キー: PAEインスタンス名（正規化後）
        - 値: MODE[7:6]の値（例: "00", "01", "10", "11"）
    
    GEN_{番号}_パターンのPAEは、FlipFlopPathSolverによって自動生成され、
    常にMODE=8'h00（パススルー）で動作するため、MODE[7:6]="00"となる。
    """
    text = open(mapped_v_path, "r", encoding="utf-8", errors="ignore").read()
    logic_to_mode2 = {}
    for m in CELL_RE.finditer(text):
        mode_hex = m.group(1)
        inst_raw = m.group(2)
        base = _norm_inst_name_basic(inst_raw)
        if not base or mode_hex is None:
            continue
        mode_val = int(mode_hex, 16) if 'h' not in mode_hex else int(mode_hex.split('h')[1], 16)
        b6 = (mode_val >> 6) & 1; b7 = (mode_val >> 7) & 1
        mode2 = f"{b7}{b6}"

        logic_to_mode2[base] = mode2
        if base.endswith('_'):
            logic_to_mode2[base.rstrip('_')] = mode2
        else:
            logic_to_mode2[base + '_'] = mode2
    
    # GEN_{番号}_パターンのPAEインスタンスを検出してデフォルトMODEを割り当て
    if bind_vars_info is not None:
        # bind_vars_infoからPAEインスタンス名を取得
        pae_instances = {instance_name for (kind, instance_name, _) in bind_vars_info if kind == "PAE"}
        
        # GEN_{番号}_パターンを検出
        gen_pattern = re.compile(r'^GEN_\d+_?$')
        for instance_name in pae_instances:
            # GEN_{番号}_パターンかどうかをチェック
            if gen_pattern.match(instance_name):
                # mapped.vに存在しない場合、デフォルトMODE（8'h00 → "00"）を割り当て
                # FlipFlopPathSolverでは常に8'h00で生成されるため、MODE[7:6]="00"
                if instance_name not in logic_to_mode2:
                    logic_to_mode2[instance_name] = "00"
                    # 名前のゆれに対応
                    if instance_name.endswith('_'):
                        logic_to_mode2[instance_name.rstrip('_')] = "00"
                    else:
                        logic_to_mode2[instance_name + '_'] = "00"
    
    return logic_to_mode2

# ====== クランプ情報生成 ======
def build_clamp_info(netlist_file, mapped_v_path):
    """
    クランプ情報（定数入力がどこに繋がっているか）を生成する。
    
    引数:
      netlist_file: .net形式のネットリストファイル
      mapped_v_path: mapped.vファイル
    
    戻り値: List[Tuple[str, int, str]]
        - 各要素は (PAEインスタンス名, 入力ポート番号, 定数値) のタプル
        - 定数値の形式: "1'b0", "1'b1", "1'h0", "1'h1" など
    
    処理内容:
    1. mapped.vからassign文で定数が割り当てられている信号を抽出
    2. .netファイルから、その定数信号がPAEの入力に接続されている箇所を検出
    """
    clamp_list = []
    
    # ===== ステップ1: mapped.vから定数信号を抽出 =====
    # assign文の正規表現パターン
    # assign <signal> = <constant>;
    assign_pattern = re.compile(r'assign\s+(\w+)\s*=\s*([0-9]+\'[bhd][0-9a-fA-F]+)\s*;', re.MULTILINE)
    
    d_assign = {}  # 信号名 -> 定数値の辞書
    
    if mapped_v_path is not None:
        try:
            with open(mapped_v_path, 'r', encoding='utf-8', errors='ignore') as f:
                text = f.read()
            
            for m in assign_pattern.finditer(text):
                signal_name = m.group(1)
                const_value = m.group(2)
                d_assign[signal_name] = const_value
        except Exception as e:
            print(f"[WARN] mapped.vの読み込みに失敗: {e}", flush=True)
    
    if not d_assign:
        # 定数信号がない場合は空リストを返す
        return clamp_list
    
    # ===== ステップ2: .netファイルからPAEの入力に定数が接続されている箇所を検出 =====
    # .netファイルのフォーマット: pae <name> <in0> <in1> <in2> <in3> <out0> <out1> <out2>
    PAE_INPUTS = 4  # PAEの入力数
    
    try:
        with open(netlist_file, 'r', encoding='utf-8') as f:
            for line in f:
                parts = line.strip().split()
                if not parts:
                    continue
                
                # コメント削除
                for i, e in enumerate(parts):
                    if '#' in e:
                        del parts[i:]
                        break
                
                if len(parts) == 0:
                    continue
                
                # pae行のみチェック
                if parts[0] == "pae" and len(parts) >= 2 + PAE_INPUTS:
                    pae_name = parts[1]
                    # 入力信号（インデックス2から2+PAE_INPUTSまで）
                    for i, input_sig in enumerate(parts[2:2+PAE_INPUTS]):
                        if input_sig in d_assign:
                            const_value = d_assign[input_sig]
                            # 不定値が入力なら警告
                            if 'x' in const_value.lower():
                                print(f"[WARN] 不定値 '{const_value}' がPAE '{pae_name}' の入力{i}に接続されています。", flush=True)
                                continue
                            
                            # クランプ情報を追加
                            clamp_list.append((pae_name, i, const_value))
    except Exception as e:
        print(f"[WARN] .netファイルの読み込みに失敗: {e}", flush=True)
    
    return clamp_list

# ====== コンフィグメモリ情報読み込み ======
def parse_config_memory_from_xml(xml_file):
    """
    XMLファイルからコンフィグメモリ情報を読み込む。
    
    引数:
      xml_file: eFPGAConnection.xmlファイルのパス
    
    戻り値: Dict[str, Any]
        - "cellIDsAll": List[int] - 全セルのIDリスト
        - "reqInputsAll": List[int] - 各セルの必要な入力ビット数
        - "hasFFAll": List[bool] - 各セルがFFを持つかのリスト
        - "nConfigBits": int - 総コンフィグビット数
        - "nConfigurableCells": int - コンフィグ可能セルの総数
    
    ConfigMemoryBuiltFromXMLと同じ処理を行う。
    """
    config_memory = {
        "cellIDsAll": [],
        "reqInputsAll": [],
        "hasFFAll": [],
        "nConfigBits": 0,
        "nConfigurableCells": 0
    }
    
    try:
        tree = ET.parse(xml_file)
        root = tree.getroot()
        
        # ConfigMemoryセクションを探す
        config_mem_elem = root.find("./ConfigMemory")
        if config_mem_elem is None:
            print(f"[WARN] ConfigMemoryセクションが見つかりません: {xml_file}", flush=True)
            return config_memory
        
        # cellIDs/item を読み込む
        e_cell_ids = config_mem_elem.findall("./cellIDs/item")
        for e_cell_id in e_cell_ids:
            if e_cell_id.text is not None:
                config_memory["cellIDsAll"].append(int(e_cell_id.text))
        
        # reqInputs/item を読み込む
        e_req_inputs = config_mem_elem.findall("./reqInputs/item")
        for e_req_input in e_req_inputs:
            if e_req_input.text is not None:
                config_memory["reqInputsAll"].append(int(e_req_input.text))
        
        # hasFF/item を読み込む
        e_has_ff = config_mem_elem.findall("./hasFF/item")
        for e_has_ff_item in e_has_ff:
            if e_has_ff_item.text is not None:
                # "True" or "False" を bool に変換
                text = e_has_ff_item.text.strip()
                if text == "True":
                    config_memory["hasFFAll"].append(True)
                elif text == "False":
                    config_memory["hasFFAll"].append(False)
                else:
                    print(f"[WARN] hasFFの値が不正です: {text}", flush=True)
                    config_memory["hasFFAll"].append(False)
        
        # nConfigBits を読み込む
        e_n_config_bits = config_mem_elem.find("nConfigBits")
        if e_n_config_bits is not None and e_n_config_bits.text is not None:
            config_memory["nConfigBits"] = int(e_n_config_bits.text)
        
        # nConfigurableCells を読み込む
        e_n_config_cells = config_mem_elem.find("nConfigurableCells")
        if e_n_config_cells is not None and e_n_config_cells.text is not None:
            config_memory["nConfigurableCells"] = int(e_n_config_cells.text)
        
    except Exception as e:
        print(f"[WARN] XMLファイルの読み込みに失敗: {e}", flush=True)
    
    return config_memory

# ====== mapped.v → 完全なMODEパラメータ抽出 ======
def parse_pae_mode_from_mapped_v(mapped_v_path, bind_vars_info=None):
    """
    mapped.vから各PAEインスタンスの完全なMODEパラメータ（8ビット）を抽出する。
    
    引数:
        mapped_v_path: mapped.vファイルのパス
        bind_vars_info: オプション。bind_vars_infoが提供された場合、GEN_{番号}_パターンの
                       PAEインスタンスを検出してデフォルトMODE（8'h00）を割り当てる。
    
    戻り値: Dict[str, str]
        - キー: PAEインスタンス名（正規化後）
        - 値: MODEパラメータの値（例: "8'h00", "8'h01"など）
    
    BitstreamGeneratorの__makePAEDictionary()と同じ処理を行う。
    GEN_{番号}_パターンのPAEは、FlipFlopPathSolverによって自動生成され、
    常にMODE=8'h00（パススルー）で動作する。
    """
    text = open(mapped_v_path, "r", encoding="utf-8", errors="ignore").read()
    logic_to_mode = {}
    
    for m in CELL_RE.finditer(text):
        mode_hex = m.group(1)  # 例: "8'h00"
        inst_raw = m.group(2)
        base = _norm_inst_name_basic(inst_raw)
        
        if not base or mode_hex is None:
            continue
        
        # 名前のゆれに対応
        logic_to_mode[base] = mode_hex
        if base.endswith('_'):
            logic_to_mode[base.rstrip('_')] = mode_hex
        else:
            logic_to_mode[base + '_'] = mode_hex
    
    # GEN_{番号}_パターンのPAEインスタンスを検出してデフォルトMODEを割り当て
    if bind_vars_info is not None:
        # bind_vars_infoからPAEインスタンス名を取得
        pae_instances = {instance_name for (kind, instance_name, _) in bind_vars_info if kind == "PAE"}
        
        # GEN_{番号}_パターンを検出
        gen_pattern = re.compile(r'^GEN_\d+_?$')
        for instance_name in pae_instances:
            # GEN_{番号}_パターンかどうかをチェック
            if gen_pattern.match(instance_name):
                # mapped.vに存在しない場合、デフォルトMODE（8'h00）を割り当て
                # FlipFlopPathSolverでは常に8'h00で生成される
                if instance_name not in logic_to_mode:
                    logic_to_mode[instance_name] = "8'h00"
                    # 名前のゆれに対応
                    if instance_name.endswith('_'):
                        logic_to_mode[instance_name.rstrip('_')] = "8'h00"
                    else:
                        logic_to_mode[instance_name + '_'] = "8'h00"
                    print(f"[GEN_PAE_MODE] {instance_name}: MODE=8'h00 (auto-assigned)", flush=True)
    
    return logic_to_mode

# ====== 名前ゆれ吸収 ======
def _variants_for_lookup(name: str):
    cand = {name}
    cand.add(name.rstrip('_'))
    cand.add(name + '_')
    cand.add(re.sub(r'_+$', '', name))
    return [x for x in cand if x]

# ====== MODE に基づく内部アーク遅延展開 ======
def build_arc_delay(bind_vars_info, logic_to_mode2):
    logic2phys = {a:b for (k,a,b) in bind_vars_info if k=="PAE"}
    phys2logic = {v:k for k,v in logic2phys.items()}
    ARC_DELAY = {}
    for pae_phys, logic in phys2logic.items():
        mode2 = logic_to_mode2.get(logic)
        if mode2 is None:
            for alt in _variants_for_lookup(logic):
                mode2 = logic_to_mode2.get(alt)
                if mode2 is not None:
                    break

        if mode2 is None:
            if logic not in _WARNED_MISSING_MODE:
                print(f"[WARN] MODE[7:6] not found for logic '{logic}'; using worst-case PAE arcs", flush=True)
                _WARNED_MISSING_MODE.add(logic)
            for (i,o), dly in _MAX_ARC.items():
                ARC_DELAY[(pae_phys, i, o)] = dly
            continue

        for pin_in, pin_out, dly in PAE_ARCS.get(mode2, []):
            i = PIN_IN_TO_IDX.get(pin_in); o = PIN_OUT_TO_IDX.get(pin_out)
            if i is None or o is None: continue
            ARC_DELAY[(pae_phys, i, o)] = dly
    return ARC_DELAY

# ====== 最悪遅延の事前計算 ======
_WARNED_MISSING_MODE = set()
_MAX_ARC = {}
for arcs in PAE_ARCS.values():
    for pin_in, pin_out, dly in arcs:
        i = PIN_IN_TO_IDX.get(pin_in)
        o = PIN_OUT_TO_IDX.get(pin_out)
        if i is None or o is None:
            continue
        key = (i, o)
        if dly > _MAX_ARC.get(key, 0.0):
            _MAX_ARC[key] = dly

# ====== connect_vars_info → クリティカルパス取得 ======
def crit_path_comb_graph(connect_vars_info, imux_fanin, omux_fanin, ARC_DELAY):
    paths = collect_all_paths(connect_vars_info, imux_fanin, omux_fanin, ARC_DELAY,
                              max_paths=10_000, max_depth=500)
    if not paths:
        return 0.0, [], (None, None, None)
    total_ns, best_edges = paths[0]
    return total_ns, best_edges, (None, None, None)

# ====== パスの遅延整形 ======
def format_path_elements(edges, imux_fanin, omux_fanin, ARC_DELAY):
    """
    edges: [(etype, src, omux, dst, w), ...]
      - PAE_ARC:  src=imuxX_Y_Z, dst=paeO_Y_Z
      - *_skip :  src=paeO_A_B,  omux=omuxK_B, dst=imuxX_C_D   （OMUX→IMUXの2要素を出力）
      - *_direct/ExtInput_to_PAE: dst=imuxX_Y_Z                 （IMUXのみ出力）
    戻り値: (表示用文字列, 合計遅延[ns])
    """
    def req_fanin(fanin_dict, name, kind):
        n = fanin_dict.get(name)
        if n is None:
            raise RuntimeError(f"Missing {kind} fanin entry for {name}")
        if n not in MUX_DELAY_MAX_NS:
            raise RuntimeError(f"Unsupported fanin {n} for {kind} {name}")
        return n

    def imux_delay(dst_imux):
        n_i = req_fanin(imux_fanin, dst_imux, "IMUX")
        return MUX_DELAY_MAX_NS[n_i]

    def omux_delay(omux):
        n_o = req_fanin(omux_fanin, omux, "OMUX")
        return MUX_DELAY_MAX_NS[n_o]

    def pae_arc_delay(src_imux, dst_pae):
        # src_imux = "imux{in}_{pid}_{lane}", dst_pae = "pae{out}_{pid}_{lane}"
        try:
            in_idx = int(src_imux.split("_")[0][4:])
            pid    = int(src_imux.split("_")[1])
            lane   = int(src_imux.split("_")[2])
            out_idx= int(dst_pae.split("_")[0][3:])
        except Exception:
            return 0.0
        key = (f"pae{pid}_{lane}", in_idx, out_idx)
        return ARC_DELAY.get(key, 0.0)

    parts = []
    total = 0.0

    for etype, src, omux, dst, _w in edges:
        if etype == "PAE_ARC":
            d = pae_arc_delay(src, dst)
            parts.append(f"{dst}({d:.2f}ns)")
            total += d

        elif etype in ("PAE_to_PAE_skip", "PAE_to_PAE_viaFF_skip"):
            d_omux = omux_delay(omux)
            parts.append(f"{omux}({d_omux:.2f}ns)")
            total += d_omux

            d_imux = imux_delay(dst)
            parts.append(f"{dst}({d_imux:.2f}ns)")
            total += d_imux

        elif etype in ("PAE_to_PAE_direct", "PAE_to_PAE_viaFF_direct", "ExtInput_to_PAE"):
            d_imux = imux_delay(dst)
            parts.append(f"{dst}({d_imux:.2f}ns)")
            total += d_imux

        elif etype == "PAE_to_ExtOutput":
            # 出力ピンは 0ns 表示にしておく（必要なら出力名を足す）
            parts.append(dst)
        else:
            # 未知タイプは無視/スキップ
            pass

    return " -> ".join(parts), total

# ====== パス整形（wなし簡易版） ======
def format_path_edges(edges, imux_fanin, omux_fanin, ARC_DELAY):
    s, tot = format_path_elements(
        [(e[0], e[1], e[2], e[3], 0.0) for e in edges],
        imux_fanin, omux_fanin, ARC_DELAY
    )
    return s, tot

# ====== 遅延評価（1配置 → クリティカルパス抽出） ======
def evaluate_delay_from_map(map, paes, raw_output_to_pae_map, external_inputs, external_outputs,
                            imux_fanin, omux_fanin, logic2mode, ff_list,
                            PI_assignments):
    bind_vars, connect_vars_info = generate_true_vars(map, paes, raw_output_to_pae_map, external_inputs, external_outputs, PI_assignments, ff_list)

    # PAE内部アーク遅延テーブル（MODEビット込み）
    ARC = build_arc_delay(bind_vars, logic2mode)

    # 全パス収集（遅延つき）
    all_paths = collect_all_paths(
        connect_vars_info, imux_fanin, omux_fanin, ARC,
        max_paths=10000, max_depth=500
    )
    if not all_paths:
        return 0.0, "", [], bind_vars, connect_vars_info

    # クリティカルパス
    best_total, best_edges = all_paths[0]

    # 表示用整形
    dbg_str, total_ns = format_path_elements(best_edges, imux_fanin, omux_fanin, ARC)

    return total_ns, dbg_str, best_edges, bind_vars, connect_vars_info

# ====== Phase-2: move-first（移動優先） ======
def lane_of(cell): return int(cell.split("_")[1])
def pid_of(cell):  return int(cell.split("_")[0][3:])

# ====== 空きセル一覧 ======
def build_free_index(placement_list, target_names):
    used = set(placement_list)
    free_by_lane = defaultdict(list)
    for cell in target_names:
        if cell not in used:
            free_by_lane[lane_of(cell)].append(cell)
    return free_by_lane

# ====== 近いレーンの空きセル探索 ======
def nearest_free(free_by_lane, target_lane):
    if not free_by_lane: return None
    best = None; best_dist = 10**9
    for ln, cells in free_by_lane.items():
        if not cells: continue
        d = abs(ln - target_lane)
        if d < best_dist:
            best_dist = d; best = (ln, cells[0])
    return best  # (lane, cell) or None

# ====== クリティカル辺の選択 ======
def choose_critical_skip_edge(crit_edges):
    skip_edges = [(etype,src,omux,dst,w) for (etype,src,omux,dst,w) in crit_edges if etype=="PAE_to_PAE_skip"]
    if skip_edges:
        return random.choice(skip_edges)
    return max(crit_edges, key=lambda e: e[4]) if crit_edges else None

# ====== パスに skip が含まれるか ======
def has_skip_on_path(crit_edges):
    return any(e[0] in ("PAE_to_PAE_skip", "PAE_to_PAE_viaFF_skip") for e in crit_edges)

# ====== クリティカルパスを改善する move 提案 ======
def propose_move(paes, placement_list, target_names, crit_edges):
    """
    （元コードのまま・docstring保持）
    """
    if not crit_edges:
        new = placement_list[:]
        i, j = random.sample(range(len(paes)), 2)
        new[i], new[j] = new[j], new[i]
        return new

    edge = choose_critical_skip_edge(crit_edges)
    if edge is None:
        new = placement_list[:]
        i, j = random.sample(range(len(paes)), 2)
        new[i], new[j] = new[j], new[i]
        return new

    etype, src, omux, dst, _ = edge

    logic_names = [p.name for p in paes]
    cur_map = {logic_names[i]: placement_list[i] for i in range(len(paes))}
    phys2logic = {v:k for k,v in cur_map.items()}
    name_to_idx = {logic_names[i]: i for i in range(len(paes))}

    src_lane = int(src.split("_")[2])
    dst_pid  = int(dst.split("_")[1]); dst_lane = int(dst.split("_")[2])
    src_pid  = int(src.split("_")[1])

    src_phys = f"pae{src_pid}_{src_lane}"
    dst_phys = f"pae{dst_pid}_{dst_lane}"
    if dst_phys not in phys2logic:
        new = placement_list[:]
        i, j = random.sample(range(len(paes)), 2)
        new[i], new[j] = new[j], new[i]
        return new

    dst_logic = phys2logic[dst_phys]
    desired_dst_lane = src_lane + 1
    desired_src_lane = dst_lane - 1

    free_by_lane = build_free_index(placement_list, target_names)
    full_packed = (len(target_names) == len(paes))

    new = placement_list[:]

    # move / swap ロジック（元コード通り）
    if src_phys in phys2logic and free_by_lane.get(desired_src_lane):
        src_logic = phys2logic[src_phys]
        idx = name_to_idx[src_logic]
        new_cell = free_by_lane[desired_src_lane].pop(0)
        new[idx] = new_cell
        return new

    if free_by_lane.get(desired_dst_lane):
        idx = name_to_idx[dst_logic]
        new_cell = free_by_lane[desired_dst_lane].pop(0)
        new[idx] = new_cell
        return new

    nf2 = nearest_free(free_by_lane, desired_src_lane)
    if nf2 is not None and src_phys in phys2logic:
        _, cell = nf2
        src_logic = phys2logic[src_phys]
        idx = name_to_idx[src_logic]
        new[idx] = cell
        return new

    nf = nearest_free(free_by_lane, desired_dst_lane)
    if nf is not None:
        _, cell = nf
        idx = name_to_idx[dst_logic]
        new[idx] = cell
        return new

    candidates2 = [c for c in target_names if lane_of(c)==desired_src_lane]
    random.shuffle(candidates2)
    for c in candidates2:
        if c in phys2logic and src_phys in phys2logic:
            other_logic = phys2logic[c]
            src_logic = phys2logic[src_phys]
            i = name_to_idx[src_logic]
            j = name_to_idx[other_logic]
            new[i], new[j] = new[j], new[i]
            return new

    candidates = [c for c in target_names if lane_of(c)==desired_dst_lane]
    random.shuffle(candidates)
    for c in candidates:
        if c in phys2logic:
            other_logic = phys2logic[c]
            i = name_to_idx[dst_logic]
            j = name_to_idx[other_logic]
            new[i], new[j] = new[j], new[i]
            return new

    if full_packed:
        i, j = random.sample(range(len(paes)), 2)
        new[i], new[j] = new[j], new[i]
        return new

    free_any = [c for lane,cells in free_by_lane.items() for c in cells]
    if free_any:
        idx = name_to_idx[dst_logic]
        new[idx] = free_any[0]
        return new

    return new

# ====== Phase-2 Simulated Annealing ======
def simulated_annealing_phase2(
    paes, target_names,
    imux_map, omux_map, ff_map, pae_to_ff_map,
    pae_output_signals, skip_count,
    norm_output_to_pae_map, raw_output_to_pae_map,
    imux_fanin, omux_fanin, logic2mode, initial_pmap,
    external_inputs, external_outputs, ff_list,
    PI_assignments,
    iterations=10000, initial_temp=100.0, min_temp=0.05, alpha=0.995
):

    import math, random
    logic_names = [p.name for p in paes]
    cur_list = [initial_pmap[name] for name in logic_names]

    # ---- パス列挙ヘルパ（構造だけ見る） ----
    def _build_graph(connect_vars_info):
        from collections import defaultdict
        adj = defaultdict(list)
        indeg = defaultdict(int)
        nodes = set()
        for (etype, src, omux, dst) in connect_vars_info:
            # 想定されるエッジタイプのみ採用（未知タイプはスキップ）
            if etype in ("PAE_to_PAE_direct", "PAE_to_PAE_skip",
                         "PAE_to_PAE_viaFF_direct", "PAE_to_PAE_viaFF_skip",
                         "ExtInput_to_PAE", "PAE_to_ExtOutput"):
                adj[src].append((dst, etype, omux))
                indeg[dst] += 1
                nodes.add(src); nodes.add(dst)
        return adj, indeg, nodes

    def _enumerate_paths(connect_vars_info, max_paths=10000, max_depth=500):
        # 返り値: [ [(etype, src, omux, dst), ...], ... ]
        adj, indeg, nodes = _build_graph(connect_vars_info)
        outdeg = {u: len(adj[u]) for u in nodes}
        starts = [n for n in nodes if indeg.get(n, 0) == 0]
        paths = []

        def dfs(u, depth, acc):
            if len(paths) >= max_paths or depth > max_depth:
                return
            if outdeg.get(u, 0) == 0:
                # 末端：経路確定
                paths.append(acc[:])
                return
            for (v, etype, omux) in adj.get(u, []):
                acc.append((etype, u, omux, v))
                dfs(v, depth + 1, acc)
                acc.pop()

        for s in starts:
            dfs(s, 0, [])
        return paths

    def _path_signature(edges):
        # 遅延値は無視して「構造のみ」で比較
        return tuple((e[0], e[1], e[2], e[3]) for e in edges)

    def _print_paths(tag, paths, limit=50):
        print(f"[{tag}] N={len(paths)}", flush=True)
        for i, edges in enumerate(paths[:limit], 1):
            # 見やすいように src->dst をつないで表示
            if not edges:
                continue
            seq = [edges[0][1]] + [e[3] for e in edges]
            print(f"  ({i:02d}) " + " -> ".join(seq), flush=True)

    # ---- 配線可能性 / 遅延評価ヘルパ ----
    def is_routable(lst):
        pmap = {logic_names[i]: lst[i] for i in range(len(paes))}
        pen, _, _ = evaluate_routability(
            pmap, paes, external_inputs,
            imux_map, omux_map, ff_map, pae_to_ff_map,
            pae_output_signals, norm_output_to_pae_map, skip_count
        )   
        return pen == 0

    def eval_delay(lst):
        pmap = {logic_names[i]: lst[i] for i in range(len(paes))}
        return evaluate_delay_from_map(
            pmap, paes, raw_output_to_pae_map, external_inputs, external_outputs,
            imux_fanin, omux_fanin, logic2mode, ff_list,
            PI_assignments=PI_assignments
        )

    # ---- 初期配置の遅延（BEFORE） ----
    cur_delay, cur_dbg, cur_edges, cur_bind, cur_conn = eval_delay(cur_list)
    print(f"[CRIT_DELAY_BEFORE] {cur_delay:.2f} ns", flush=True)
    print(f"[CRIT_PATH_BEFORE] {cur_dbg}", flush=True)

    # 全パス（構造）を列挙して表示（上位50本のみ）
    try:
        paths_before = _enumerate_paths(cur_conn, max_paths=10000, max_depth=500)
        _print_paths("ALL_PATHS_BEFORE", paths_before, limit=50)
    except Exception as e:
        print(f"[ALL_PATHS_BEFORE][ERROR] {e}", flush=True)
        paths_before = []

    best_delay, best_list, best_dbg, best_bind, best_conn = cur_delay, cur_list[:], cur_dbg, cur_bind, cur_conn

    # ---- Phase-2 SAループ ----
    T = initial_temp
    it = 0
    while it < iterations:
        # クリティカルパスが SkipOMUX を使っていないなら終了
        if not has_skip_on_path(cur_edges):
            print("[PHASE2_INFO] Critical path uses no SkipOMUX. Delay optimization finished.", flush=True)
            break
        it += 1
        cand_list = propose_move(paes, cur_list, target_names, cur_edges)

        # まず配線可能性
        if not is_routable(cand_list):
            T = max(min_temp, T * alpha)
            continue

        # 遅延評価（主評価）
        cand_delay, cand_dbg, cand_edges, cand_bind, cand_conn = eval_delay(cand_list)

        improve = cand_delay < cur_delay
        accept = improve or (random.random() < math.exp(-(cand_delay - cur_delay) / max(T, 1e-9)))

        if accept:
            cur_list, cur_delay, cur_dbg, cur_edges, cur_bind, cur_conn = \
                cand_list, cand_delay, cand_dbg, cand_edges, cand_bind, cand_conn
            if cand_delay < best_delay:
                best_delay, best_list, best_dbg, best_bind, best_conn = \
                    cand_delay, cand_list[:], cand_dbg, cand_bind, cand_conn

        T = max(min_temp, T * alpha)

    # ---- 結果（AFTER） ----
    best_map = {logic_names[i]: best_list[i] for i in range(len(paes))}
    print(f"[CRIT_DELAY_AFTER]  {best_delay:.2f} ns", flush=True)
    print(f"[CRIT_PATH_AFTER]  {best_dbg}", flush=True)

    # AFTER での全パス列挙＆ BEFORE との一致チェック
    try:
        paths_after = _enumerate_paths(best_conn, max_paths=10000, max_depth=500)
        _print_paths("ALL_PATHS_AFTER", paths_after, limit=50)

        sig_before = { _path_signature(p) for p in paths_before }
        sig_after  = { _path_signature(p) for p in paths_after }
        common = sig_before & sig_after
        print(f"[ALL_PATHS_CHECK] before={len(sig_before)} after={len(sig_after)} same={len(common)}", flush=True)

        missing = sig_before - sig_after
        added   = sig_after  - sig_before
        if missing:
            print(f"[ALL_PATHS_DIFF] missing_from_after={len(missing)}", flush=True)
        if added:
            print(f"[ALL_PATHS_DIFF] added_in_after={len(added)}", flush=True)
    except Exception as e:
        print(f"[ALL_PATHS_AFTER][ERROR] {e}", flush=True)

    return best_map, best_delay, best_dbg, best_bind, best_conn, it, (cur_delay, cur_dbg)

# ==============================================================
#  SECTION4: Bind / Connect（最終配置から変数生成）
# ==============================================================
# ====== Bind/Connect 変数生成 ======
def generate_true_vars(best_placement, paes, output_to_pae_map, external_inputs, external_outputs, PI_assignments, ff_list):
    # PAE/PI/PO の BindVar と、全接続の ConnectVar を生成
    bind_vars_info = []
    connect_vars_info = []
    pae_dict = {pae.name: pae for pae in paes}

    # --- BindVar（PAE配置） ---
    for instance_name, target_name in best_placement.items():
        bind_vars_info.append(("PAE", instance_name, target_name))

    # --- BindVar（外部入力PI配置） ---
    for signal, assigned_pi in PI_assignments.items():
        bind_vars_info.append(("PI", signal, assigned_pi))

    # --- 外部出力：BindVar + ConnectVar ---
    for (src_logical, port), out_signal in external_outputs.items():
        target_name = best_placement[src_logical]
        pae_id = int(target_name.split("_")[0][3:])
        pae_y = int(target_name.split("_")[1])
        efpga_o_idx = pae_id * 3 + port
        bind_vars_info.append(("PO", out_signal, f"EFPGA_O[{efpga_o_idx}]"))
        connect_vars_info.append(("PAE_to_ExtOutput", f"pae{port}_{pae_id}_{pae_y}", None, f"EFPGA_O[{efpga_o_idx}]"))

    # --- 生産者表（信号を出すPAE） ---
    producer = {}
    for pae in paes:
        for out_port, out_sig in pae.outputs.items():
            producer.setdefault(out_sig, []).append((pae.name, out_port))

    # --- FF の Q→D 変換 ---
    ff_q_to_d = {q_sig: d_sig for (_ff, d_sig, q_sig) in ff_list}
    ff_q_set  = set(ff_q_to_d.keys())

    # --- SkipOMUX割り当て管理 ---
    skip_omux_map = {}      # (src_lane, src_sig) -> omux_idx
    omux_count_by_lane = {} # lane -> next omux idx

    seen = set()

    # --- 各信号の接続を生成 ---
    for sink_sig, sinks in output_to_pae_map.items():
        is_via_ff = sink_sig in ff_q_set
        src_signal = ff_q_to_d.get(sink_sig, sink_sig)

        for (src_logic, out_port) in producer.get(src_signal, []):
            if src_logic not in best_placement:
                continue
            src_ph = best_placement[src_logic]
            src_id   = int(src_ph.split("_")[0][3:])
            src_lane = int(src_ph.split("_")[1])
            src_with_port = f"pae{out_port}_{src_id}_{src_lane}"

            for (dst_logic, dst_in_port) in sinks:
                if dst_logic not in best_placement:
                    continue
                dst_ph = best_placement[dst_logic]
                dst_id   = int(dst_ph.split("_")[0][3:])
                dst_lane = int(dst_ph.split("_")[1])
                dst_imux = f"imux{dst_in_port}_{dst_id}_{dst_lane}"

                # --- 同一レーン（direct） ---
                if dst_lane == src_lane + 1:
                    conn_type = "PAE_to_PAE_viaFF_direct" if is_via_ff else "PAE_to_PAE_direct"
                    item = (conn_type, src_with_port, None, dst_imux)

                # --- レーン跨ぎ（skip） ---
                else:
                    key = (src_lane, src_signal)
                    if key not in skip_omux_map:
                        omux_idx = omux_count_by_lane.get(src_lane, 0)
                        skip_omux_map[key] = omux_idx
                        omux_count_by_lane[src_lane] = omux_idx + 1
                    else:
                        omux_idx = skip_omux_map[key]
                    omux = f"omux{omux_idx}_{src_lane}"
                    conn_type = "PAE_to_PAE_viaFF_skip" if is_via_ff else "PAE_to_PAE_skip"
                    item = (conn_type, src_with_port, omux, dst_imux)

                if item not in seen:
                    connect_vars_info.append(item)
                    seen.add(item)

    # --- ConnectVar（外部入力） ---
    for signal, connections in external_inputs.items():
        if signal not in PI_assignments:
            continue
        src = PI_assignments[signal]
        for pae_name, input_port in connections:
            if pae_name not in best_placement:
                continue
            dst_physical = best_placement[pae_name]
            dst_id = int(dst_physical.split("_")[0][3:])
            dst_y = int(dst_physical.split("_")[1])
            imux = f"imux{input_port}_{dst_id}_{dst_y}"
            connect_vars_info.append(("ExtInput_to_PAE", src, None, imux))

    return bind_vars_info, connect_vars_info


# --------------------------
#  Bind/Connect 出力ユーティリティ
# --------------------------
def dump_connect_vars_py(connect_vars_info, out_py_path="connect_vars.py"):
    with open(out_py_path, "w", encoding="utf-8") as f:
        f.write("# auto-generated\nconnect_vars_info = [\n")
        for etype, src, omux, dst in connect_vars_info:
            f.write(f"    ({etype!r}, {src!r}, {None if omux is None else repr(omux)}, {dst!r}),\n")
        f.write("]\n")
    print(f"[CONNECT_VARS_PY] {out_py_path}", flush=True)

def dump_bind_vars_py(bind_vars_info, out_py_path="bind_vars.py"):
    with open(out_py_path, "w", encoding="utf-8") as f:
        f.write("# auto-generated\nbind_vars_info = [\n")
        for kind, a, b in bind_vars_info:
            f.write(f"    ({kind!r}, {a!r}, {b!r}),\n")
        f.write("]\n")
    print(f"[BIND_VARS_PY] {out_py_path}", flush=True)

def build_pae_has_ffs(bind_vars_info, connect_vars_info, ff_list, paes, pae_to_ff_map=None):
    """
    PAEインスタンスの各出力がFlipFlopを使用しているかを判定する。
    
    戻り値: Dict[str, List[bool]]
        - キー: PAEインスタンス名
        - 値: [hasFF0, hasFF1, hasFF2] (各出力ポートがFFを使用しているか)
    
    判定方法:
    1. ff_listから、FFのD信号を出力しているPAEを特定
    2. connect_vars_infoでviaFFの接続がある場合も、FFを使用していることを示す
    3. pae_to_ff_mapが提供されている場合（oneff.xml対応）、1つのffnodeに対して1つのPAE出力のみがFFを使うように判定
    """
    # PAEインスタンス名 -> [hasFF0, hasFF1, hasFF2] の辞書
    pae_has_ffs = {}
    
    # まず、すべてのPAEインスタンスを初期化（デフォルトはFalse）
    for kind, instance_name, _ in bind_vars_info:
        if kind == "PAE":
            pae_has_ffs[instance_name] = [False, False, False]
    
    # --- 方法1: ff_listから、FFのD信号を出力しているPAEを特定 ---
    # FFのD信号を出力しているPAEを特定
    ff_d_signals = {d_sig for (_ff, d_sig, _q) in ff_list}
    
    # 信号を出力しているPAEを特定（producer表を作成）
    producer = {}
    for pae in paes:
        for out_port, out_sig in pae.outputs.items():
            producer.setdefault(out_sig, []).append((pae.name, out_port))
    
    # FFのD信号を出力しているPAEの出力ポートをマーク
    for d_sig in ff_d_signals:
        if d_sig in producer:
            for pae_name, out_port in producer[d_sig]:
                if pae_name in pae_has_ffs and 0 <= out_port < 3:
                    pae_has_ffs[pae_name][out_port] = True
    
    # --- 方法2: connect_vars_infoでviaFFの接続がある場合もFFを使用 ---
    # viaFFの接続がある場合、そのPAE出力もFFを使用している
    for etype, src, omux, dst in connect_vars_info:
        if etype in ("PAE_to_PAE_viaFF_direct", "PAE_to_PAE_viaFF_skip"):
            # src = "pae{out_port}_{pid}_{lane}" の形式
            if src.startswith("pae") and "_" in src:
                try:
                    # pae{out_port}_{pid}_{lane} から out_port を抽出
                    parts = src.split("_")
                    if len(parts) >= 3:
                        out_port_str = parts[0][3:]  # "pae" を除いた部分
                        out_port = int(out_port_str)
                        
                        # pidとlaneからPAEインスタンス名を逆引き
                        # bind_vars_infoから物理PAEセル名 -> 論理インスタンス名のマップを作成
                        phys_to_logic = {}
                        for kind, logic_name, phys_name in bind_vars_info:
                            if kind == "PAE":
                                phys_to_logic[phys_name] = logic_name
                        
                        # srcから物理PAEセル名を抽出
                        pid = int(parts[1])
                        lane = int(parts[2])
                        phys_pae = f"pae{pid}_{lane}"
                        
                        if phys_pae in phys_to_logic:
                            logic_name = phys_to_logic[phys_pae]
                            if logic_name in pae_has_ffs and 0 <= out_port < 3:
                                pae_has_ffs[logic_name][out_port] = True
                except (ValueError, IndexError):
                    # パースエラーは無視
                    pass
    
    # --- 方法3: oneff.xml対応 - pae_to_ff_mapを使って、1つのffnodeに対して1つのPAE出力のみがFFを使うように判定 ---
    if pae_to_ff_map is not None:
        # oneff.xmlでは、1つのffnodeに複数のPAE出力が接続可能だが、実際にFFを使うのは1つのPAE出力のみ
        # connect_vars_infoのPAE_to_PAE_viaFF情報とff_listから、実際にFFを使うPAE出力を特定
        
        # bind_vars_infoから物理PAEセル名 -> 論理インスタンス名のマップを作成
        phys_to_logic = {}
        for kind, logic_name, phys_name in bind_vars_info:
            if kind == "PAE":
                phys_to_logic[phys_name] = logic_name
        
        # 方法2で既に設定された情報をクリア（oneff.xml対応で上書きするため）
        # ただし、方法1（ff_listから）で設定された情報は保持
        
        # ff_listからFFのD信号を特定し、その信号を生成するPAE出力を優先的に選択
        # これが最も確実な方法
        ffnode_to_ff_pae = {}  # ffnode名 -> (logic_name, out_port)
        
        # ff_listからFFのD信号を取得
        ff_d_signals = {d_sig: (_ff, d_sig, _q) for (_ff, d_sig, _q) in ff_list}
        
        # 信号を出力しているPAEを特定（producer表を作成）
        producer = {}
        for pae in paes:
            for out_port, out_sig in pae.outputs.items():
                producer.setdefault(out_sig, []).append((pae.name, out_port))
        
        # FFのD信号を生成するPAE出力とffnodeの対応を構築
        for d_signal, (_ff, _d, _q) in ff_d_signals.items():
            # d_signalを生成するPAE出力を特定
            for pae_name, out_port in producer.get(d_signal, []):
                # このPAE出力がどのffnodeに接続されているかをpae_to_ff_mapから探す
                for kind, logic_name, phys_name in bind_vars_info:
                    if kind == "PAE" and logic_name == pae_name:
                        # 物理PAEセル名からpae_output_nameを構築
                        parts = phys_name.split("_")
                        if len(parts) >= 2:
                            pid = int(parts[0][3:])  # "pae"を除く
                            lane = int(parts[1])
                            pae_output_name = f"pae{out_port}_{pid}_{lane}"
                            
                            # pae_to_ff_mapからffnode名を取得
                            if pae_output_name in pae_to_ff_map:
                                ffnode_name = pae_to_ff_map[pae_output_name]
                                # FFのD信号を生成するPAE出力を優先
                                if ffnode_name not in ffnode_to_ff_pae:
                                    ffnode_to_ff_pae[ffnode_name] = (logic_name, out_port)
                                    break
        
        # 方法2で設定された情報をクリア（oneff.xml対応で上書き）
        # 各ffnodeに対して、1つのPAE出力のみをFFに使用
        for ffnode_name in set(pae_to_ff_map.values()):
            # このffnodeに接続されているすべてのPAE出力をクリア
            for pae_output_name in pae_to_ff_map:
                if pae_to_ff_map[pae_output_name] == ffnode_name:
                    try:
                        parts = pae_output_name.split("_")
                        if len(parts) >= 3:
                            out_port = int(parts[0][3:])
                            pid = int(parts[1])
                            lane = int(parts[2])
                            phys_pae = f"pae{pid}_{lane}"
                            
                            if phys_pae in phys_to_logic:
                                logic_name = phys_to_logic[phys_pae]
                                # 方法2で設定された情報をクリア
                                if logic_name in pae_has_ffs and 0 <= out_port < 3:
                                    pae_has_ffs[logic_name][out_port] = False
                    except (ValueError, IndexError):
                        pass
        
        # 実際にFFを使うPAE出力のみを設定
        for ffnode_name, (logic_name, out_port) in ffnode_to_ff_pae.items():
            if logic_name in pae_has_ffs and 0 <= out_port < 3:
                pae_has_ffs[logic_name][out_port] = True
                print(f"[PAE_HAS_FFS] {logic_name}[{out_port}] -> {ffnode_name} (oneff: selected)", flush=True)
    
    return pae_has_ffs

def dump_true_vars_txt(bind_vars_info, connect_vars_info, out_path="true_vars.txt"):
    """
    bind_vars_infoとconnect_vars_infoからtrue_vars.txt形式のファイルを生成する。
    
    形式:
    - b_{instance}_{target}: BindVar（PAE配置、PI配置、PO配置）
    - c_{src}--{omux}--{dst}: ConnectVar（OMUX経由）
    - c_{src}--{dst}: ConnectVar（OMUXなし）
    - w_{src}--{omux}--{dst}: WireVar（c_と同じ内容）
    - w_{src}--{dst}: WireVar（c_と同じ内容）
    - u_{src}--{omux}: OMUXUseVar（OMUX使用）
    """
    lines = ["True Variables:"]
    
    # --- BindVar（b_で始まる行） ---
    for kind, a, b in bind_vars_info:
        if kind == "PAE":
            # b_{instance_name}_{target_name}
            lines.append(f"b_{a}_{b}")
        elif kind == "PI":
            # b_{signal}_{PI_name}
            lines.append(f"b_{a}_{b}")
        elif kind == "PO":
            # b_{signal}_{PO_name}
            lines.append(f"b_{a}_{b}")
    
    # --- ConnectVar（c_で始まる行） ---
    # OMUX使用のマップを作成（u_行の生成用）
    omux_usage = set()
    
    for etype, src, omux, dst in connect_vars_info:
        if omux is not None:
            # c_{src}--{omux}--{dst}
            lines.append(f"c_{src}--{omux}--{dst}")
            # OMUX使用を記録
            omux_usage.add((src, omux))
        else:
            # c_{src}--{dst}
            lines.append(f"c_{src}--{dst}")
    
    # --- WireVar（w_で始まる行、c_と同じ内容） ---
    for etype, src, omux, dst in connect_vars_info:
        if omux is not None:
            # w_{src}--{omux}--{dst}
            lines.append(f"w_{src}--{omux}--{dst}")
        else:
            # w_{src}--{dst}
            lines.append(f"w_{src}--{dst}")
    
    # --- OMUXUseVar（u_で始まる行） ---
    for src, omux in sorted(omux_usage):
        lines.append(f"u_{src}--{omux}")
    
    # ファイルに書き込み
    with open(out_path, "w", encoding="utf-8") as f:
        f.write("\n".join(lines) + "\n")
    
    print(f"[TRUE_VARS_TXT] {out_path}", flush=True)

# レポート用
def report_file(path, placement_map, delay_ns, dbg_str):
    with open(path, "w", encoding="utf-8") as f:
        f.write("[PLACEMENT]\n")
        for k in sorted(placement_map.keys()):
            f.write(f"{k} -> {placement_map[k]}\n")
        f.write("\n[CRITICAL_PATH]\n")
        f.write(f"CRIT_DELAY_NS: {delay_ns:.3f}\n")
        f.write(f"CRIT_PATH: {dbg_str}\n")


# ==============================================================
#  SECTION5: Critical Path / Path Enumeration Utilities
# ==============================================================
def dump_all_paths_once(connect_vars_info, imux_fanin, omux_fanin, ARC_DELAY,
                        max_paths=200, max_depth=200):
    from collections import defaultdict

    adj = defaultdict(list); indeg = defaultdict(int); nodes=set()

    # 使われている PAE 出力ノードだけ拾う（src が pae{out}_{pid}_{lane} のもの）
    used_pae_out = set()
    for etype, src, omux, dst in connect_vars_info:
        if isinstance(src, str) and src.startswith("pae"):
            used_pae_out.add(src)

    def req_fanin(fanin_dict, name, kind):
        n = fanin_dict.get(name)
        if n is None: raise RuntimeError(f"Missing {kind} fanin entry for {name}")
        if n not in MUX_DELAY_MAX_NS: raise RuntimeError(f"Unsupported fanin {n} for {kind} {name}")
        return n

    def edge_ns(etype, src, omux, dst):
        if etype in ("PAE_to_PAE_skip", "PAE_to_PAE_viaFF_skip"):
            n_o = req_fanin(omux_fanin, omux, "OMUX")
            n_i = req_fanin(imux_fanin, dst, "IMUX")
            return MUX_DELAY_MAX_NS[n_o] + MUX_DELAY_MAX_NS[n_i]
        elif etype in ("PAE_to_PAE_direct", "PAE_to_PAE_viaFF_direct", "ExtInput_to_PAE"):
            n_i = req_fanin(imux_fanin, dst, "IMUX")
            return MUX_DELAY_MAX_NS[n_i]
        elif etype == "PAE_to_ExtOutput":
            return 0.0
        else:
            raise RuntimeError(f"Unknown edge type {etype}")

    def add_edge(u,v,w,info):
        adj[u].append((v,w,info)); indeg[v]+=1; nodes.add(u); nodes.add(v)

    # 接続エッジ
    for (etype, src, omux, dst) in connect_vars_info:
        if etype in ("PAE_to_PAE_direct", "PAE_to_PAE_skip",
                     "PAE_to_PAE_viaFF_direct", "PAE_to_PAE_viaFF_skip",
                     "ExtInput_to_PAE", "PAE_to_ExtOutput"):
            w = edge_ns(etype, src, omux, dst)
            add_edge(src, dst, w, (etype, src, omux, dst, w))

    # IMUX→PAE出力（※“使われている出力”だけに限定！）
    for node in list(nodes):
        if isinstance(node, str) and node.startswith("imux"):
            parts = node.split("_")
            in_idx = int(parts[0][4:]); pid = int(parts[1]); lane = int(parts[2])
            pae_phys = f"pae{pid}_{lane}"
            for out_idx in (0,1,2):
                dst = f"pae{out_idx}_{pid}_{lane}"
                if dst not in used_pae_out:  # ★ここで未使用出力を除外
                    continue
                key = (pae_phys, in_idx, out_idx)
                if key not in ARC_DELAY:
                    continue
                w = ARC_DELAY[key]
                add_edge(node, dst, w, ("PAE_ARC", node, None, dst, w))

    outdeg = {u: len(adj[u]) for u in nodes}
    starts = [n for n in nodes if indeg.get(n,0)==0]

    # EFPGA_O を終点とする
    def is_sink(u: str) -> bool:
        return isinstance(u, str) and u.startswith("EFPGA_O[")

    all_paths = []
    def dfs(u, depth, acc_w, acc_edges, seen):
        if depth > max_depth: return
        if is_sink(u):
            all_paths.append((acc_w, acc_edges[:]))
            return
        for v,w,info in adj.get(u,[]):
            if v in seen: continue
            seen.add(v); acc_edges.append(info)
            dfs(v, depth+1, acc_w+w, acc_edges, seen)
            acc_edges.pop(); seen.remove(v)

    for s in starts:
        dfs(s, 0, 0.0, [], {s})

    if not all_paths:
        print("[ALL_PATHS] (no complete path to EFPGA_O)")
        return

    all_paths.sort(key=lambda x: x[0], reverse=True)
    print("[ALL_PATHS]")
    limit = min(max_paths, len(all_paths))
    for i in range(limit):
        tot, edges = all_paths[i]
        s, total = format_path_elements(edges, imux_fanin, omux_fanin, ARC_DELAY)
        print(f"  {s}")

def collect_all_paths(connect_vars_info, imux_fanin, omux_fanin, ARC_DELAY,
                      max_paths=10_000, max_depth=500):
    from collections import defaultdict

    # --- helpers ---
    def req_fanin(fanin_dict, name, kind):
        n = fanin_dict.get(name)
        if n is None:
            raise RuntimeError(f"Missing {kind} fanin entry for {name}")
        if n not in MUX_DELAY_MAX_NS:
            raise RuntimeError(f"Unsupported fanin {n} for {kind} {name}")
        return n

    def edge_delay(info):
        etype, src, omux, dst = info
        if etype in ("PAE_to_PAE_skip", "PAE_to_PAE_viaFF_skip"):
            n_o = req_fanin(omux_fanin, omux, "OMUX")
            n_i = req_fanin(imux_fanin, dst,  "IMUX")
            return MUX_DELAY_MAX_NS[n_o] + MUX_DELAY_MAX_NS[n_i]
        elif etype in ("PAE_to_PAE_direct", "PAE_to_PAE_viaFF_direct", "ExtInput_to_PAE"):
            n_i = req_fanin(imux_fanin, dst, "IMUX")
            return MUX_DELAY_MAX_NS[n_i]
        elif etype == "PAE_to_ExtOutput":
            return 0.0
        elif etype == "PAE_ARC":
            # dst = pae{out}_{pid}_{lane}, src = imux{in}_{pid}_{lane}
            try:
                in_idx  = int(src.split("_")[0][4:])
                pid     = int(src.split("_")[1])
                lane    = int(src.split("_")[2])
                out_idx = int(dst.split("_")[0][3:])
            except Exception:
                return 0.0
            key = (f"pae{pid}_{lane}", in_idx, out_idx)
            return ARC_DELAY.get(key, 0.0)
        else:
            raise RuntimeError(f"Unknown edge type {etype}")

    # --- build graph: connect edges ---
    adj = defaultdict(list)
    indeg = defaultdict(int)
    nodes = set()
    allowed = {
        "PAE_to_PAE_direct", "PAE_to_PAE_skip",
        "PAE_to_PAE_viaFF_direct", "PAE_to_PAE_viaFF_skip",
        "ExtInput_to_PAE", "PAE_to_ExtOutput",
    }

    used_pae_out = set()
    for (etype, src, omux, dst) in connect_vars_info:
        if etype in allowed:
            info = (etype, src, omux, dst)
            adj[src].append((dst, info))
            indeg[dst] += 1
            nodes.add(src); nodes.add(dst)
        if isinstance(src, str) and src.startswith("pae"):
            used_pae_out.add(src)

    # --- add PAE internal arcs: IMUX -> used PAE outputs only ---
    for node in list(nodes):
        if isinstance(node, str) and node.startswith("imux"):
            parts = node.split("_")
            if len(parts) != 3: 
                continue
            in_idx = int(parts[0][4:])
            pid    = int(parts[1])
            lane   = int(parts[2])
            pae_phys = f"pae{pid}_{lane}"
            for out_idx in (0, 1, 2):
                dst = f"pae{out_idx}_{pid}_{lane}"
                if dst not in used_pae_out:
                    continue
                key = (pae_phys, in_idx, out_idx)
                if key not in ARC_DELAY:
                    continue
                info = ("PAE_ARC", node, None, dst)
                adj[node].append((dst, info))
                indeg[dst] += 1
                nodes.add(node); nodes.add(dst)

    # --- DFS enumerate simple paths to EFPGA_O[...] ---
    def is_sink(u):
        return isinstance(u, str) and u.startswith("EFPGA_O[")

    starts = [n for n in nodes if indeg.get(n, 0) == 0]
    all_paths = []
    seen_sigs = set()

    def sig_of(edges):
        return tuple((e[0], e[1], e[2], e[3]) for e in edges)

    def dfs(u, depth, acc_w, acc_edges, seen_nodes):
        if len(all_paths) >= max_paths or depth > max_depth:
            return
        if is_sink(u):
            s = sig_of(acc_edges)
            if s not in seen_sigs:
                seen_sigs.add(s)
                all_paths.append((acc_w, acc_edges[:]))
            return
        for v, info in adj.get(u, []):
            if v in seen_nodes:
                continue
            w = edge_delay(info)
            seen_nodes.add(v); acc_edges.append((*info, w))
            dfs(v, depth+1, acc_w + w, acc_edges, seen_nodes)
            acc_edges.pop(); seen_nodes.remove(v)

    for s in starts:
        dfs(s, 0, 0.0, [], {s})

    all_paths.sort(key=lambda x: x[0], reverse=True)
    return all_paths


# =============================================================
#  SECTION6: トップレベルドライバ（Phase1/Phase2 を呼ぶ）
# =============================================================
def run_sa_pnr(netlist_file, xml_file, mapped_v, generate_bitstream_flag=False):
    """
    SAベースで配置・配線 (Phase-1) を行い，
    DELAY=True のときは Phase-2（遅延最適化）まで実行するドライバ関数。

    他スクリプトからは基本的にこの関数を呼ぶ。
    戻り値: bind_vars_info, connect_vars_info

    引数:
      netlist_file : .net 形式の PAE ネットリスト
      xml_file     : eFPGAConnection.xml
      mapped_v     : mapped.v（DELAY=True のとき必須, DELAY=False のとき省略可/None）
      generate_bitstream_flag : ビットストリーム生成を実行するか（デフォルト: False）
    """
    start = time.time()
    random.seed(2)

    # ===== SECTION1: XML 解析 =====
    (imux_map, omux_map, ff_map, pae_to_ff_map,
     skip_count, target_names, pae_output_signals,
     nPIs, imux_fanin, omux_fanin) = parse_fpga_connection_all(xml_file)
    print("[IMUX_MAP]")
    print(imux_map)
    print("[OMUX_MAP]")
    print(omux_map)    
    print("[FF_MAP]")
    print(ff_map)
    print("[PAE_TO_FF_MAP]")
    print(pae_to_ff_map)
    print("[SKIP_COUNT]")
    print(skip_count)
    print("[TARGET_NAMES]")
    print(target_names)
    print("[PAE_OUTPUT_SIGNALS]")
    print(pae_output_signals)
    print("[NPI]")
    print(nPIs)
    print("[IMUX_FANIN]")
    print(imux_fanin)
    print("[OMUX_FANIN]")
    print(omux_fanin)
    print("====parse_fpga_connection_all=====")

    # ===== SECTION1: ネットリスト解析 =====
    (paes, external_inputs, external_outputs,
     raw_output_to_pae_map, ff_list, norm_output_to_pae_map) = read_netlist(netlist_file, nPIs)
    print("====read_netlist=====")
    print("[PAES]")
    print(paes)
    print("[EXTERNAL_INPUTS]")
    print(external_inputs)
    print("[EXTERNAL_OUTPUTS]")
    print(external_outputs)
    print("[RAW_OUTPUT_TO_PAE_MAP]")
    print(raw_output_to_pae_map)
    print("[FF_LIST]")
    print(ff_list)
    print("[NORM_OUTPUT_TO_PAE_MAP]")
    print(norm_output_to_pae_map)
    print("====read_netlist=====")

    # ===== SECTION2: Phase-1（配線可能化）=====
    print("====simulated_annealing_phase1=====")
    routable_map, PI_assignments = simulated_annealing_phase1(
        paes, external_inputs, target_names,
        imux_map, omux_map, ff_map, pae_to_ff_map,
        pae_output_signals, skip_count,
        norm_output_to_pae_map,
        max_iters=500000, initial_temp=100
    )
    print("====simulated_annealing_phase1=====")
    print("[ROUTABLE_MAP]")
    print(routable_map)
    print("[PI_ASSIGNMENTS]")
    print(PI_assignments)
    print("====simulated_annealing_phase1=====")
    t1 = time.time()
    print(f"[PHASE1_TIME] {t1 - start:.3f} s", flush=True)
    print("[PHASE1_DONE] Routable placement completed.", flush=True)

    # ===== Phase-1 結果から bind/connect を生成 =====
    bind_vars_info, connect_vars_info = generate_true_vars(
        routable_map, paes, raw_output_to_pae_map,
        external_inputs, external_outputs, PI_assignments, ff_list
    )
    print("====generate_true_vars=====")
    print("[BIND_VARS_INFO]")
    print(bind_vars_info)
    print("[CONNECT_VARS_INFO]")
    print(connect_vars_info)
    print("====generate_true_vars=====")



    # ===== DELAY=False → Phase-1 のみ =====
    if not DELAY:
        if mapped_v is None:
            # mapped.v が無い場合は遅延評価そのものをスキップ
            print("[INFO] DELAY=False & mapped.v not provided → delay evaluation is skipped.", flush=True)
            print(f"[PAE_NODES] {len(routable_map)}", flush=True)
            print("[PnR_RESULT] Succeed", flush=True)
            
            # ===== true_vars.txt を出力 =====
            dump_true_vars_txt(bind_vars_info, connect_vars_info, "true_vars.txt")
            
            # ===== PAEのFlipFlop利用情報を生成 =====
            # pae_to_ff_mapを取得（oneff.xml対応のため）
            _, _, _, pae_to_ff_map_local, _, _, _, _, _, _ = parse_fpga_connection_all(xml_file)
            pae_has_ffs = build_pae_has_ffs(bind_vars_info, connect_vars_info, ff_list, paes, pae_to_ff_map=pae_to_ff_map_local)
            print("[PAE_HAS_FFS]")
            for pae_name, has_ffs in sorted(pae_has_ffs.items()):
                print(f"  {pae_name}: {has_ffs}")
            
            # ===== PAEのConfig情報（MODEパラメータ）を取得 =====
            if mapped_v is not None:
                pae_mode_dict = parse_pae_mode_from_mapped_v(mapped_v, bind_vars_info)
                print("[PAE_MODE_CONFIG]")
                # bind_vars_infoから論理PAE名を取得
                logic2phys = {a: b for (k, a, b) in bind_vars_info if k == "PAE"}
                for logic_name, phys_name in sorted(logic2phys.items()):
                    mode = pae_mode_dict.get(logic_name)
                    if mode is None:
                        # 名前のゆれに対応
                        for alt in _variants_for_lookup(logic_name):
                            mode = pae_mode_dict.get(alt)
                            if mode is not None:
                                break
                    if mode is not None:
                        print(f"  {logic_name} -> {phys_name}: MODE={mode}")
                    else:
                        print(f"  {logic_name} -> {phys_name}: MODE=NOT_FOUND")
            else:
                print("[PAE_MODE_CONFIG] mapped.v が指定されていないため、MODE情報を取得できません。")
            
            # ===== クランプ情報を生成 =====
            clamp_info = build_clamp_info(netlist_file, mapped_v)
            print("[CLAMP_INFO]")
            if clamp_info:
                for pae_name, pos, clamp_val in sorted(clamp_info):
                    print(f"  {pae_name}: input[{pos}] = {clamp_val}")
            else:
                print("  (クランプ情報なし)")
            
            # ===== コンフィグメモリ情報を読み込み =====
            config_memory = parse_config_memory_from_xml(xml_file)
            print("[CONFIG_MEMORY]")
            print(f"  nConfigurableCells: {config_memory['nConfigurableCells']}")
            print(f"  nConfigBits: {config_memory['nConfigBits']}")
            print(f"  cellIDsAll: {len(config_memory['cellIDsAll'])} items")
            print(f"  reqInputsAll: {len(config_memory['reqInputsAll'])} items")
            print(f"  hasFFAll: {len(config_memory['hasFFAll'])} items")
            if len(config_memory['cellIDsAll']) > 0:
                print(f"  (例) cellID[0]={config_memory['cellIDsAll'][0]}, reqInputs[0]={config_memory['reqInputsAll'][0]}, hasFF[0]={config_memory['hasFFAll'][0]}")
            
            return bind_vars_info, connect_vars_info

        # mapped.v があるなら Phase-1 結果の遅延だけ測る
        print("[INFO] DELAY=False → Phase-1 の配置で遅延のみ評価", flush=True)
        logic2mode = parse_logic_mode_from_mapped_v(mapped_v, bind_vars_info)
        ARC = build_arc_delay(bind_vars_info, logic2mode)
        crit_ns, crit_edges, _ = crit_path_comb_graph(
            connect_vars_info, imux_fanin, omux_fanin, ARC
        )
        dbg_str, total_ns = format_path_edges(crit_edges, imux_fanin, omux_fanin, ARC)

        print(f"[PAE_NODES] {len(routable_map)}", flush=True)
        print(f"[CRIT_DELAY_AFTER] {total_ns:.2f} ns", flush=True)
        print(f"[CRIT_PATH] {dbg_str}", flush=True)
        print("[PnR_RESULT] Succeed", flush=True)
        
        # ===== true_vars.txt を出力 =====
        dump_true_vars_txt(bind_vars_info, connect_vars_info, "true_vars.txt")
        
        # ===== PAEのFlipFlop利用情報を生成 =====
        pae_has_ffs = build_pae_has_ffs(bind_vars_info, connect_vars_info, ff_list, paes, pae_to_ff_map=pae_to_ff_map)
        print("[PAE_HAS_FFS]")
        for pae_name, has_ffs in sorted(pae_has_ffs.items()):
            print(f"  {pae_name}: {has_ffs}")
        
        # ===== PAEのConfig情報（MODEパラメータ）を取得 =====
        if mapped_v is not None:
            pae_mode_dict = parse_pae_mode_from_mapped_v(mapped_v, bind_vars_info)
            print("[PAE_MODE_CONFIG]")
            # bind_vars_infoから論理PAE名を取得
            logic2phys = {a: b for (k, a, b) in bind_vars_info if k == "PAE"}
            for logic_name, phys_name in sorted(logic2phys.items()):
                mode = pae_mode_dict.get(logic_name)
                if mode is None:
                    # 名前のゆれに対応
                    for alt in _variants_for_lookup(logic_name):
                        mode = pae_mode_dict.get(alt)
                        if mode is not None:
                            break
                if mode is not None:
                    print(f"  {logic_name} -> {phys_name}: MODE={mode}")
                else:
                    print(f"  {logic_name} -> {phys_name}: MODE=NOT_FOUND")
        else:
            print("[PAE_MODE_CONFIG] mapped.v が指定されていないため、MODE情報を取得できません。")
        
        # ===== クランプ情報を生成 =====
        clamp_info = build_clamp_info(netlist_file, mapped_v)
        print("[CLAMP_INFO]")
        if clamp_info:
            for pae_name, pos, clamp_val in sorted(clamp_info):
                print(f"  {pae_name}: input[{pos}] = {clamp_val}")
        else:
            print("  (クランプ情報なし)")
        
        # ===== コンフィグメモリ情報を読み込み =====
        config_memory = parse_config_memory_from_xml(xml_file)
        print("[CONFIG_MEMORY]")
        print(f"  nConfigurableCells: {config_memory['nConfigurableCells']}")
        print(f"  nConfigBits: {config_memory['nConfigBits']}")
        print(f"  cellIDsAll: {len(config_memory['cellIDsAll'])} items")
        print(f"  reqInputsAll: {len(config_memory['reqInputsAll'])} items")
        print(f"  hasFFAll: {len(config_memory['hasFFAll'])} items")
        if len(config_memory['cellIDsAll']) > 0:
            print(f"  (例) cellID[0]={config_memory['cellIDsAll'][0]}, reqInputs[0]={config_memory['reqInputsAll'][0]}, hasFF[0]={config_memory['hasFFAll'][0]}")
        
        return bind_vars_info, connect_vars_info

    # ===== DELAY=True → Phase-2（遅延最適化）=====
    if mapped_v is None:
        print("[ERROR] DELAY=True ですが mapped.v が指定されていません。", file=sys.stderr, flush=True)
        sys.exit(1)

    print("[INFO] DELAY=True → Phase-2（遅延最適化）を実行", flush=True)

    # mapped.v から MODE[7:6] を取得
    # 注意: Phase-2ではbind_vars_infoはPhase-1の結果を使用
    logic2mode = parse_logic_mode_from_mapped_v(mapped_v, bind_vars_info)

    # ===== SECTION3: Phase-2 SA（遅延最適化）=====
    best_map, best_delay, best_dbg, _b, _c, it2, (_init_dly, _init_dbg) = simulated_annealing_phase2(
        paes, target_names,
        imux_map, omux_map, ff_map, pae_to_ff_map,
        pae_output_signals, skip_count,
        norm_output_to_pae_map, raw_output_to_pae_map,
        imux_fanin, omux_fanin, logic2mode, routable_map,
        external_inputs, external_outputs, ff_list,
        PI_assignments=PI_assignments,
        iterations=10000, initial_temp=100.0, min_temp=0.05, alpha=0.995
    )
    print(f"[SA_ITER_PHASE2] {it2}", flush=True)

    # ===== 最終 bind/connect & クリティカルパス =====
    bind_vars_info, connect_vars_info = generate_true_vars(
        best_map, paes, raw_output_to_pae_map,
        external_inputs, external_outputs, PI_assignments, ff_list
    )

    ARC = build_arc_delay(bind_vars_info, logic2mode)
    crit_ns, crit_edges, _ = crit_path_comb_graph(connect_vars_info, imux_fanin, omux_fanin, ARC)
    dbg_str, total_ns = format_path_edges(crit_edges, imux_fanin, omux_fanin, ARC)

    print(f"[PAE_NODES] {len(best_map)}", flush=True)
    print(f"[CRIT_DELAY_AFTER] {total_ns:.2f} ns", flush=True)
    print(f"[CRIT_PATH] {dbg_str}", flush=True)
    print("[PnR_RESULT] Succeed", flush=True)

    # ===== true_vars.txt を出力 =====
    dump_true_vars_txt(bind_vars_info, connect_vars_info, "true_vars.txt")
    
    # ===== PAEのFlipFlop利用情報を生成 =====
    pae_has_ffs = build_pae_has_ffs(bind_vars_info, connect_vars_info, ff_list, paes)
    print("[PAE_HAS_FFS]")
    for pae_name, has_ffs in sorted(pae_has_ffs.items()):
        print(f"  {pae_name}: {has_ffs}")
    
    # ===== PAEのConfig情報（MODEパラメータ）を取得 =====
    if mapped_v is not None:
        pae_mode_dict = parse_pae_mode_from_mapped_v(mapped_v, bind_vars_info)
        print("[PAE_MODE_CONFIG]")
        # bind_vars_infoから論理PAE名を取得
        logic2phys = {a: b for (k, a, b) in bind_vars_info if k == "PAE"}
        for logic_name, phys_name in sorted(logic2phys.items()):
            mode = pae_mode_dict.get(logic_name)
            if mode is None:
                # 名前のゆれに対応
                for alt in _variants_for_lookup(logic_name):
                    mode = pae_mode_dict.get(alt)
                    if mode is not None:
                        break
            if mode is not None:
                print(f"  {logic_name} -> {phys_name}: MODE={mode}")
            else:
                print(f"  {logic_name} -> {phys_name}: MODE=NOT_FOUND")
    else:
        print("[PAE_MODE_CONFIG] mapped.v が指定されていないため、MODE情報を取得できません。")
    
    # ===== クランプ情報を生成 =====
    clamp_info = build_clamp_info(netlist_file, mapped_v)
    print("[CLAMP_INFO]")
    if clamp_info:
        for pae_name, pos, clamp_val in sorted(clamp_info):
            print(f"  {pae_name}: input[{pos}] = {clamp_val}")
    else:
        print("  (クランプ情報なし)")
    
    # ===== コンフィグメモリ情報を読み込み =====
    config_memory = parse_config_memory_from_xml(xml_file)
    print("[CONFIG_MEMORY]")
    print(f"  nConfigurableCells: {config_memory['nConfigurableCells']}")
    print(f"  nConfigBits: {config_memory['nConfigBits']}")
    print(f"  cellIDsAll: {len(config_memory['cellIDsAll'])} items")
    print(f"  reqInputsAll: {len(config_memory['reqInputsAll'])} items")
    print(f"  hasFFAll: {len(config_memory['hasFFAll'])} items")
    if len(config_memory['cellIDsAll']) > 0:
        print(f"  (例) cellID[0]={config_memory['cellIDsAll'][0]}, reqInputs[0]={config_memory['reqInputsAll'][0]}, hasFF[0]={config_memory['hasFFAll'][0]}")

    print("出力情報")
    print(bind_vars_info)
    print()
    print(connect_vars_info)
    
    # ===== ビットストリーム生成（オプション） =====
    # 環境変数 BITSTREAM_GEN=1 が設定されている場合、または generate_bitstream_flag=True の場合に実行
    import os
    should_generate_bitstream = generate_bitstream_flag or (os.getenv("BITSTREAM_GEN") == "1")
    if should_generate_bitstream:
        print("\n[BITSTREAM_GEN] Bitstream generation is enabled.", flush=True)
        # pae_to_ff_mapを取得（oneff.xml対応のため）
        _, _, _, pae_to_ff_map_for_bitstream, _, _, _, _, _, _ = parse_fpga_connection_all(xml_file)
        
        # 必要な情報を準備
        pae_has_ffs = build_pae_has_ffs(bind_vars_info, connect_vars_info, ff_list, paes, pae_to_ff_map=pae_to_ff_map_for_bitstream)
        pae_mode_dict = parse_pae_mode_from_mapped_v(mapped_v, bind_vars_info) if mapped_v else {}
        clamp_info = build_clamp_info(netlist_file, mapped_v) if mapped_v else []
        
        # 出力パス
        base_name = os.path.splitext(os.path.basename(netlist_file))[0]
        output_bit_path = f"{base_name}.bit"
        
        # ビットストリーム生成
        success = generate_bitstream(
            bind_vars_info,
            connect_vars_info,
            pae_has_ffs,
            pae_mode_dict,
            clamp_info,
            netlist_file,
            mapped_v,
            xml_file,
            output_bit_path,
            paes,
            external_inputs,
            external_outputs,
            ff_list,
            pae_to_ff_map=pae_to_ff_map_for_bitstream
        )
        
        if success:
            print(f"[BITSTREAM_GEN] Successfully generated: {output_bit_path}", flush=True)
        else:
            print("[BITSTREAM_GEN] Bitstream generation failed.", flush=True)
    else:
        print("[BITSTREAM_GEN] Bitstream generation is disabled. Set BITSTREAM_GEN=1 or use --bitstream flag to enable.", flush=True)

    return bind_vars_info, connect_vars_info

# =============================================================
#  SECTION7: ビットストリーム生成（SATmgrを使わない実装）
# =============================================================
# ====== SATVarクラス（SATmgrを使わない実装） ======
class SimpleVarManager:
    """SATmgrの代わりに使う簡易マネージャー（SATソルバーを実行しない）"""
    def __init__(self):
        self.vars = {}  # count -> Var の辞書

class Var:
    """SAT変数の基底クラス"""
    count = 1
    
    def __init__(self, mgr=None):
        self.count = Var.count
        Var.count += 1
        self.mgr = mgr if mgr is not None else SimpleVarManager()
        if hasattr(self.mgr, 'vars'):
            self.mgr.vars[self.count] = self
    
    @classmethod
    def numVars(cls):
        return cls.count
    
    def cnfStr(self):
        return "{}".format(self.count)
    
    @property
    def name(self):
        raise NotImplementedError("Subclass must implement name property")

class BindVar(Var):
    """PAEインスタンスを物理PAEセルにバインドする変数"""
    def __init__(self, mgr, instance, target):
        super().__init__(mgr)
        self.instance = instance  # Netlistのnode(PAEInstance, netlistPI/PO)
        self.target = target      # PAE Logicのブロック(PAECell, PI/PO)
    
    @property
    def name(self):
        name = "b_" + self.instance.name + "_" + self.target.name
        return name

class ConnectVar(Var):
    """接続を表す変数"""
    def __init__(self, mgr, src, omux, dst):
        super().__init__(mgr)
        self.src = src
        self.omux = omux
        self.dst = dst
    
    @property
    def name(self):
        name = "c_" + self.src.name
        if self.omux is not None:
            name += "--" + self.omux.name
        name += "--" + self.dst.name
        return name


        
def generate_net_file_for_bitstream(netlist_file, paes, external_inputs, external_outputs, ff_list, output_path="netlist_for_bitstream.net"):
    """
    .netファイルを生成する（BitstreamGenerator用）
    
    引数:
        netlist_file: 元の.netファイルパス（inputs/outputs/const/ff情報を取得）
        paes: PAEオブジェクトのリスト
        external_inputs: 外部入力の辞書
        external_outputs: 外部出力の辞書
        ff_list: FFリスト
        output_path: 出力ファイルパス
    """
    # 元の.netファイルからinputs/outputs/const/ff情報を読み込む
    defined_inputs = set()
    defined_outputs = set()
    const_signals = set()
    
    with open(netlist_file, 'r', encoding='utf-8') as f:
        for line in f:
            parts = line.strip().split()
            if not parts:
                continue
            if parts[0] == "inputs":
                defined_inputs = set(parts[1:])
            elif parts[0] == "outputs":
                defined_outputs = set(parts[1:])
            elif parts[0] == "const":
                if len(parts) > 1:
                    const_signals.add(parts[1])
    
    # .netファイルを生成
    with open(output_path, 'w', encoding='utf-8') as f:
        # PAEinputs/PAEoutputs
        f.write("PAEinputs 4\n")
        f.write("PAEoutputs 3\n\n")
        
        # inputs
        f.write("inputs")
        for inp in sorted(defined_inputs):
            f.write(f" {inp}")
        f.write("\n")
        
        # outputs
        f.write("outputs")
        for out in sorted(defined_outputs):
            f.write(f" {out}")
        f.write("\n\n")
        
        # const
        for const_sig in sorted(const_signals):
            f.write(f"const {const_sig}\n")
        if const_signals:
            f.write("\n")
        
        # ff
        for ff_name, d_sig, q_sig in ff_list:
            f.write(f"ff {ff_name} {d_sig} {q_sig}\n")
        if ff_list:
            f.write("\n")
        
        # pae
        for pae in paes:
            f.write("pae")
            f.write(f" {pae.name}")
            # 入力（4つ）
            for i in range(4):
                sig = pae.inputs.get(i, "nc")
                if sig in const_signals:
                    sig = "nc"
                f.write(f" {sig}")
            # 出力（3つ）
            for i in range(3):
                sig = pae.outputs.get(i, "nc")
                if sig in const_signals:
                    sig = "nc"
                f.write(f" {sig}")
            f.write("\n")
    
    print(f"[NET_FILE] Generated: {output_path}", flush=True)
    return output_path

def generate_bitstream(
    bind_vars_info,
    connect_vars_info,
    pae_has_ffs,
    logic_to_mode,
    clamp_info,
    netlist_file,
    mapped_v_path,
    connection_xml_path,
    output_bit_path,
    paes,
    external_inputs,
    external_outputs,
    ff_list,
    pae_to_ff_map=None
):
    """
    ビットストリーム生成のメイン関数
    """
    import sys
    import os
    from pathlib import Path

    # efpga_toolsのパスを追加
    efpga_tools_path = Path(__file__).parent.parent.parent
    sys.path.insert(0, str(efpga_tools_path))
    
    # =========================================================
    # 強力なモジュールリロード処理
    # =========================================================
    # "BitstreamGen" で始まるすべての読み込み済みモジュールを強制的に破棄します。
    # これにより、クラス定義の混在を確実に防ぎます。
    prefix = "BitstreamGen"
    modules_to_remove = [m for m in sys.modules if m.startswith(prefix)]
    for m in modules_to_remove:
        del sys.modules[m]

    # =========================================================
    # モジュールの差し替え（モンキーパッチ）
    # =========================================================
    import types
    # 偽の SATVar モジュールを作成
    satvar_module = types.ModuleType('BitstreamGen.SatPR.SATVar')
    satvar_module.Var = Var
    satvar_module.BindVar = BindVar
    satvar_module.ConnectVar = ConnectVar
    
    # sys.modules に登録して、ファイルからの読み込みをブロック＆置換
    sys.modules['BitstreamGen.SatPR.SATVar'] = satvar_module
    
    try:
        # ここで初めてインポート（キャッシュが消えているので、偽モジュールを使って再構築される）
        from pyverilog.vparser.parser import parse
        from BitstreamGen.SatPR import NetList
        from BitstreamGen.ImportPAEArray.PAEArrayFromFile import PAEArrayFromFile
        from BitstreamGen.ImportConfigMemory.ConfigMemoryFromFile import ConfigMemoryFromFile
        from BitstreamGen.GenBitstream.BitstreamGenerator import BitstreamGenerator
        from BitstreamGen.SatPR.NetList import clampPAEin
        import pyverilog.vparser.ast as defast
        
        # デバッグ: クラスが正しく置き換わっているか確認
        import BitstreamGen.SatPR.SATVar as LoadedSATVar
        if LoadedSATVar.BindVar is not BindVar:
            print("[ERROR] Class mismatch! Patch failed.", flush=True)
        else:
            print("[BITSTREAM_GEN] Class patch successful.", flush=True)

        print("[BITSTREAM_GEN] Starting bitstream generation...", flush=True)
        
        # 1. .netファイルの生成
        net_file_for_bitstream = generate_net_file_for_bitstream(
            netlist_file, paes, external_inputs, external_outputs, ff_list
        )
        
        # 2. astmapの生成
        print("[BITSTREAM_GEN] Parsing mapped.v...", flush=True)
        astmap, _ = parse([mapped_v_path], debug=False)
        
        # 3. l_Clampの生成
        print("[BITSTREAM_GEN] Building clamp information...", flush=True)
        l_Clamp = [
            clampPAEin(key=pae_name, pos=port, clamp=const_value)
            for pae_name, port, const_value in clamp_info
        ]
        
        # 4. glueGenの生成
        print("[BITSTREAM_GEN] Loading config memory from XML...", flush=True)
        glueGen = ConfigMemoryFromFile(connection_xml_path)
        
        # 5. PAEArrayの構築
        print("[BITSTREAM_GEN] Building PAEArray from XML...", flush=True)
        pa = PAEArrayFromFile(connection_xml_path)
        
        # 6. Netlistの構築
        print("[BITSTREAM_GEN] Building Netlist from .net file...", flush=True)
        base_name = os.path.splitext(os.path.basename(mapped_v_path))[0]
        netlist = NetList.Netlist(net_file_for_bitstream, mapped_v_path)
        netlist.checkNet(pa)
        
        # 6-1. GEN_* PAEインスタンスの追加処理（元のコードと同じ）
        print("[BITSTREAM_GEN] Adding GEN_* PAE instances to astmap...", flush=True)
        gen_pattern = re.compile(r'^GEN_\d+_?$')
        gen_pae_instances = []
        for kind, instance_name, _ in bind_vars_info:
            if kind == "PAE" and gen_pattern.match(instance_name):
                gen_pae_instances.append(instance_name)
        
        if gen_pae_instances:
            module_def = None
            for definition in astmap.description.definitions:
                if isinstance(definition, defast.ModuleDef):
                    module_def = definition
                    break
            
            if module_def is not None:
                # efpga_tools内のパスを解決するためにsys.pathが必要
                from BitstreamGen.PostProcess.ReplaceFFClass.PAECell import PAECellFactory
                pae_factory = PAECellFactory()
                
                high_clamp_name = None
                for item in module_def.items:
                    if isinstance(item, defast.Assign):
                        if hasattr(item.right, 'var') and hasattr(item.right.var, 'value'):
                            if item.right.var.value == "1'h1":
                                high_clamp_name = item.left.var.name
                                break
                if high_clamp_name is None:
                    for item in module_def.items:
                        if isinstance(item, defast.Assign):
                            if hasattr(item.right, 'var') and hasattr(item.right.var, 'value'):
                                if '1' in item.right.var.value:
                                    high_clamp_name = item.left.var.name
                                    break
                
                for gen_pae_name in gen_pae_instances:
                    if gen_pae_name in netlist.PAEInstances:
                        pae_instance = netlist.PAEInstances[gen_pae_name]
                        input_signals = []
                        for i in range(4):
                            if i in pae_instance.inputs:
                                input_signals.append(pae_instance.inputs[i].name)
                            else:
                                if high_clamp_name:
                                    input_signals.append(high_clamp_name)
                                else:
                                    input_signals.append("1'b1")
                        
                        output_signals = []
                        if 0 in pae_instance.outputs:
                            output_signals.append(pae_instance.outputs[0].name)
                        
                        gen_pae_cell = pae_factory.BuildPAECell(
                            gen_pae_name, "8'h00", input_signals, output_signals
                        )
                        
                        mutable_items = list(module_def.items)
                        insert_pos = len(mutable_items)
                        for i, item in enumerate(mutable_items):
                            if isinstance(item, defast.InstanceList):
                                insert_pos = i + 1
                        mutable_items.insert(insert_pos, gen_pae_cell.astPAE)
                        module_def.items = tuple(mutable_items)
                        print(f"[BITSTREAM_GEN] Added GEN PAE instance: {gen_pae_name}", flush=True)

        # 7. hasFFs 設定
        print("[BITSTREAM_GEN] Setting PAE hasFFs information...", flush=True)
        for pae_instance_name, has_ffs_list in pae_has_ffs.items():
            if pae_instance_name in netlist.PAEInstances:
                pae_instance = netlist.PAEInstances[pae_instance_name]
                for i, has_ff in enumerate(has_ffs_list):
                    if i < len(pae_instance.hasFFs):
                        pae_instance.hasFFs[i] = has_ff
        
        # 7-1. oneff.xml対応 (ffnode追加)
        if pae_to_ff_map is not None:
            print("[BITSTREAM_GEN] Adding ffnode connections...", flush=True)
            ffnode_map = {}
            for cell in pa.PAECells:
                for output in cell.outputs:
                    for dst in output.dsts:
                        if hasattr(dst, 'name') and dst.name.startswith('ffnode'):
                            ffnode_map[dst.name] = dst
            
            # 物理名から論理名を逆引きするマップ
            phys_to_logic = {}
            for kind, logic_name, phys_name in bind_vars_info:
                if kind == "PAE":
                    phys_to_logic[phys_name] = logic_name

            for pae_output_name, ffnode_name in pae_to_ff_map.items():
                try:
                    parts = pae_output_name.split("_")
                    if len(parts) >= 3:
                        out_port = int(parts[0][3:])
                        pid = int(parts[1])
                        lane = int(parts[2])
                        phys_pae = f"pae{pid}_{lane}"
                        
                        pae_cell = next((c for c in pa.PAECells if c.name == phys_pae), None)
                        if pae_cell and out_port < len(pae_cell.outputs):
                            pae_output = pae_cell.outputs[out_port]
                            if ffnode_name in ffnode_map:
                                ffnode = ffnode_map[ffnode_name]
                                if ffnode not in pae_output.dsts:
                                    pae_output.AddDst(ffnode)
                except Exception:
                    pass

        # 8. trueVarsの構築
        print("[BITSTREAM_GEN] Building trueVars (without SATmgr)...", flush=True)
        var_mgr = SimpleVarManager()
        trueVars = []
        
        pae_cell_map = {cell.name: cell for cell in pa.PAECells}
        pi_map = {pi.name: pi for pi in pa.PIs}
        po_map = {po.name: po for po in pa.POs}
        
        interconnect_src_map = {}
        interconnect_omux_map = {}
        interconnect_dst_map = {}
        
        for ic in pa.Interconnects:
            if ic.src: interconnect_src_map[ic.src.name] = ic.src
            if ic.omux: interconnect_omux_map[ic.omux.name] = ic.omux
            if ic.dst: interconnect_dst_map[ic.dst.name] = ic.dst
        
        for kind, instance_name, target_name in bind_vars_info:
            if kind == "PAE":
                if instance_name in netlist.PAEInstances:
                    inst = netlist.PAEInstances[instance_name]
                    tgt = pae_cell_map.get(target_name)
                    if tgt: trueVars.append(BindVar(var_mgr, inst, tgt))
            elif kind == "PI":
                if instance_name in netlist.netlistPIs:
                    inst = netlist.netlistPIs[instance_name]
                    tgt = pi_map.get(target_name)
                    if tgt: trueVars.append(BindVar(var_mgr, inst, tgt))
            elif kind == "PO":
                if instance_name in netlist.netlistPOs:
                    inst = netlist.netlistPOs[instance_name]
                    tgt = po_map.get(target_name)
                    if tgt: trueVars.append(BindVar(var_mgr, inst, tgt))
        
        for etype, src_str, omux_str, dst_str in connect_vars_info:
            src_obj = interconnect_src_map.get(src_str)
            omux_obj = interconnect_omux_map.get(omux_str) if omux_str else None
            dst_obj = interconnect_dst_map.get(dst_str)
            
            if src_obj and dst_obj:
                trueVars.append(ConnectVar(var_mgr, src_obj, omux_obj, dst_obj))
            else:
                # 見つからない場合は警告
                print(f"[WARN] ConnectVar object not found: {src_str} -> {omux_str} -> {dst_str}", flush=True)

        print(f"[BITSTREAM_GEN] Found {len(trueVars)} trueVars", flush=True)
        
        # 9. BitstreamGeneratorの呼び出し
        print("[BITSTREAM_GEN] Generating bitstream...", flush=True)
        # pae_to_ff_mapを渡して、allff.xmlとoneff.xmlを区別できるようにする
        bg = BitstreamGenerator(trueVars, astmap, l_Clamp, glueGen, pae_to_ff_map=pae_to_ff_map)
        bg.GenerateBitstream(output_bit_path, "OneBit")
        
        print(f"[BITSTREAM_GEN] Bitstream generated: {output_bit_path}", flush=True)
        return True
        
    except Exception as e:
        print(f"[ERROR] Bitstream generation failed: {e}", file=sys.stderr, flush=True)
        import traceback
        traceback.print_exc()
        return False

if __name__ == "__main__":
    import sys
    import argparse
    
    parser = argparse.ArgumentParser(description="SA-based Placement and Routing for eFPGA")
    parser.add_argument("netlist_file", help=".net形式のPAEネットリストファイル")
    parser.add_argument("xml_file", help="eFPGAConnection.xmlファイル")
    parser.add_argument("mapped_v", nargs="?", default=None, help="mapped.vファイル（DELAY=Trueのとき必須）")
    parser.add_argument("--bitstream", action="store_true", help="ビットストリーム生成を実行する")
    
    args = parser.parse_args()
    
    run_sa_pnr(args.netlist_file, args.xml_file, args.mapped_v, generate_bitstream_flag=args.bitstream)

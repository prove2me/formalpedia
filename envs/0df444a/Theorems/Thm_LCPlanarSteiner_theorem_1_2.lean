-- Prove2me | Theorems.Thm_LCPlanarSteiner_theorem_1_2
-- name    : LCPlanarSteiner.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:07:06.231767+00:00
-- url     : https://prove2.me/theorems/c16e5b7d-a8db-45c0-b463-935defaeaaec
-- title:
--   Theorem 1.2 — planar directed Steiner forest: paths $\le (1+\varepsilon)h$ at cost $O(\varepsilon^{-2}\log^7(2q))\,\mathrm{OPT}^F_h$ and $19968(w+1)\varepsilon^{-1}D_q^6\,\mathrm{OPT}^F_{h,w}$
-- statement:
--   Let $G = (V, E)$ be a planar directed graph with nonnegative rational arc costs $c_e$ and lengths $\ell_e$, encoded in binary; cycles, parallel and antiparallel arcs and zero costs or lengths are allowed. Let $h \ge 0$ and $0 < \varepsilon \le 1$ be rational, and let $(s_i, t_i)$, $i \in [q]$, $q \ge 1$, be an indexed list of demand pairs. A **strict forest** is a set $S$ of arcs containing, for every $i$, a path from $s_i$ to $t_i$ of length at most $h$; $\mathrm{OPT}^F_h$ is the least cost $c(S) = \sum_{e \in S} c_e$ of a strict forest, and $\mathrm{OPT}^F_{h,w}$ the least cost of one whose simple underlying undirected graph has treewidth at most $w$ ($+\infty$ if none). Write $D_q = 1 + \lceil \log_2 q \rceil$.
--
--   **Theorem 1.2 (Forest guarantee).** There is a deterministic algorithm, running in time polynomial jointly in the complete binary input and $1/\varepsilon$, which on every strictly feasible instance returns simple paths $P_i : s_i \rightsquigarrow t_i$ with
--   $$
--   \ell(P_i) \le (1 + \varepsilon)h \qquad (i \in [q]),
--   $$
--   whose shared union $F$ (each arc paid once) satisfies
--   $$
--   c(F) \le \frac{23\,721\,984\, D_q^7}{\varepsilon^2}\, \mathrm{OPT}^F_h = O\bigl(\varepsilon^{-2}\log^7(2q)\bigr)\, \mathrm{OPT}^F_h
--   $$
--   and, simultaneously for every $w \ge 0$,
--   $$
--   c(F) \le \frac{19968\,(w + 1)}{\varepsilon}\, D_q^6\, \mathrm{OPT}^F_{h,w} .
--   $$
--   Neither $w$ nor a reference decomposition is an input. The constant is $79872 \cdot C_{NE}$ with $C_{NE} = 11 C_E = 297$ (proof of Theorem 1.2, p.16).
--
--   The previous directed planar guarantee (Chekuri–Jain 2026) violated lengths by an $O(\log q)$ factor; here lengths are violated by a factor $1 + \varepsilon$ only.
--
--   **Formalization Note** The algorithm is one function on all instances, computed by a Turing machine (`Turing.TM2ComputableInPolyTime`) on the binary encoding padded by $\lceil 1/\varepsilon \rceil$ symbols. The optima are compared through every strict forest $S$.
--
--   Differences from the source:
--   - generalization: c(F) ≤ O(ε^{−2} log^7(2q)) OPT^F_h → c(F) ≤ 23721984 · D_q^7/ε² · c(S) for every strict forest S; reason: the explicit constant is the paper's own last display (p.16), 79872·C_NE with C_NE = 11·27 = 297; since log₂(2q) ≤ D_q ≤ 2 log₂(2q) for q ≥ 1, the explicit bound implies the O-form
--   - generalization: returns original paths P_i : s_i ⇝ t_i → returns simple paths; reason: the proof's pair paths are cycle-erased (p.15), and a simple path is an original path
--   - reading: a deterministic algorithm whose running time is polynomial jointly in the complete binary input and 1/ε → one function computed by a Turing machine in time polynomial in the length of the binary instance padded by ⌈1/ε⌉ symbols; reason: the paper names no machine model; TM2 machines are deterministic, and the padding makes the input length the binary size plus 1/ε up to one
--   - encoding: OPT^F_h; OPT^F_{h,w} simultaneously for every finite width comparator → every strict forest S; every w : ℕ and every strict forest S whose simple underlying graph has treewidth ≤ w, quantified after the output; reason: both optima are minima over finitely many arc sets, and OPT^F_{h,w} = ∞ makes its clause vacuous; neither w nor S is an input
--   - encoding: a shared union F; planar G; strictly feasible instances; q ≥ 1 indexed demands → F = the union of the arcs of the returned paths; planarity of the simple underlying graph of all arcs; the hypothesis that all arcs form a strict forest; a valid instance with a nonempty demand list (vertices 0, …, n−1, arcs by list position); reason: any union containing the paths costs at least as much; loops and parallel arcs are always drawable; Lean convention, same instances
-- source:
--   Mahboub, Rahgoshay, Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar Graphs, STOC 2027 submission (manuscript sha256 5af18346c1fe696ca8ed57aa7736510e10e27188695bb15edcbe662315790dda), Theorem 1.2, p.2; explicit constant, proof of Theorem 1.2, p.16; C_E = 27, C_NE = 11C_E, Lemma 4.3, pp.12–13; model, §1, p.2

import Mathlib
import Definitions.Def_LCPlanarSteiner_Inst
import Definitions.Def_LCPlanarSteiner_IsSPath
import Definitions.Def_LCPlanarSteiner_plen
import Definitions.Def_LCPlanarSteiner_pcost
import Definitions.Def_LCPlanarSteiner_StrictForest
import Definitions.Def_LCPlanarSteiner_underlying
import Definitions.Def_LCPlanarSteiner_Dlog
import Definitions.Def_LCPlanarSteiner_encIn
import Definitions.Def_LCPlanarSteiner_encPaths
import Definitions.Def_RobertsonSeymour1986_GM5_IsPlanar
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE

namespace LCPlanarSteiner

/-- **Theorem 1.2 (Forest guarantee).**
Mahboub, Rahgoshay, *Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar
Graphs*, STOC 2027 submission (manuscript sha256 5af18346…), Theorem 1.2, p.2: "For planar directed
Steiner forest with q ≥ 1 indexed demands, a deterministic algorithm returns original paths
P_i : s_i ⇝ t_i in a shared union F such that c(F) ≤ O(ε^{−2} log^7(2q)) OPT^F_h,
ℓ(P_i) ≤ (1 + ε)h (i ∈ [q]). Its running time is polynomial jointly in the complete binary input and
1/ε. Writing D_q = 1 + ⌈log_2 q⌉, the same output also satisfies
c(F) ≤ 19968(w + 1)ε^{−1}D_q^6 OPT^F_{h,w} simultaneously for every finite width comparator."
Explicit constant: proof of Theorem 1.2, p.16, "Thus c(F) ≤ 79872C_NE D_q^7/ε² OPT^F_h", with
`C_NE = 11 C_E` and `C_E = 27` (Lemma 4.3, pp.12–13), so `79872 · 297 = 23721984`.

There is one function `alg` from instances to lists of arc-index paths, computable by a Turing
machine in time polynomial in the length of `encIn I` (the binary instance padded by `⌈1/ε⌉`
symbols), such that for every valid instance whose underlying graph is planar and in which every
demand has an original path of length `≤ h`:
1. `alg I` has one path per demand, and the `i`-th is a simple path of `G` from `s_i` to `t_i` of
   length `≤ (1 + ε)h`;
2. the union `F` of the arcs of these paths costs `c(F) ≤ 23721984 · D_q^7 / ε² · c(S)` for every
   strict forest `S`;
3. for every `w` and every strict forest `S` whose underlying simple graph has treewidth `≤ w`,
   `c(F) ≤ 19968 (w + 1) / ε · D_q^6 · c(S)`.

**Formalization Note.** The machine is fixed before the instance (`∃ alg` precedes `∀ I`); TM2 is
deterministic. `OPT^F_h` and `OPT^F_{h,w}` are compared through "every strict forest `S`" (and "every
`S` of underlying treewidth `≤ w`", vacuous when `OPT^F_{h,w} = ∞`); `w` and `S` are quantified
after the output is fixed, so neither is an input. The explicit `23721984 · D_q^7` implies the
printed `O(ε^{−2} log^7(2q))`, since `log₂(2q) ≤ D_q ≤ 2 log₂(2q)` for `q ≥ 1`. -/
theorem theorem_1_2 :
    ∃ alg : Inst → List (List ℕ),
      Nonempty (Turing.TM2ComputableInPolyTime encIn encPaths alg) ∧
      ∀ I : Inst, I.Valid →
        RobertsonSeymour1986.GM5.IsPlanar (underlying I.net I.net.allArcs) →
        StrictForest I.net I.dem I.h I.net.allArcs →
        (alg I).length = I.dem.length ∧
        (∀ i < I.dem.length,
          IsSPath I.net (I.dem.getD i (0, 0)).1 (I.dem.getD i (0, 0)).2 ((alg I).getD i []) ∧
          plen I.net ((alg I).getD i []) ≤ (1 + I.ε) * I.h) ∧
        (∀ S : Finset ℕ, StrictForest I.net I.dem I.h S →
          pcost I.net (alg I).flatten.toFinset ≤
            23721984 * (Dlog I.dem.length : ℚ) ^ 7 / I.ε ^ 2 * pcost I.net S) ∧
        (∀ (w : ℕ) (S : Finset ℕ), StrictForest I.net I.dem I.h S →
          RobertsonSeymour1986.GM5.TreewidthLE (underlying I.net S) w →
          pcost I.net (alg I).flatten.toFinset ≤
            19968 * ((w : ℚ) + 1) / I.ε * (Dlog I.dem.length : ℚ) ^ 6 * pcost I.net S) := by sorry

end LCPlanarSteiner

-- Prove2me | Theorems.Thm_LCPlanarSteiner_Supplement_theorem_1_1
-- name    : LCPlanarSteiner.Supplement.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:17:37.302418+00:00
-- url     : https://prove2.me/theorems/c9a19861-8cd7-4817-9930-d9353f3c15ef
-- title:
--   Theorem 1.1 — planar rooted directed Steiner tree: paths $\le (1+\varepsilon)h$ at cost $O(\varepsilon^{-1}\log^2(2k))\,\mathrm{OPT}_h$ and $O(\varepsilon^{-1}\log^3(2k))\,\mathrm{LP}_h$
-- statement:
--   Let $G = (V, E)$ be a planar directed graph with nonnegative rational arc costs $c_e$ and lengths $\ell_e$, encoded in binary; cycles, parallel and antiparallel arcs and zero costs or lengths are allowed. Let $h \ge 0$ and $0 < \varepsilon \le 1$ be rational. In **rooted directed Steiner tree** a root $r$ must reach every terminal of a set $T$ by an original path of length at most $h$; $k$ is the number of terminals other than $r$, and $D = 1 + \lceil \log_2 k \rceil$. Buying $F \subseteq E$ costs $c(F) = \sum_{e \in F} c_e$ (shared arcs paid once). $\mathrm{OPT}_h$ is the least cost of an arc set containing such a path to every terminal, and $\mathrm{LP}_h$ is the value of the strict path-flow relaxation
--   $$
--   \mathrm{LP}_h = \min \sum_e c_e x_e \quad \text{s.t.} \quad \sum_{p \in P_h(t)} f^t_p = 1 \ (t \in T), \qquad \sum_{p \in P_h(t):\, e \in p} f^t_p \le x_e \ (e \in E,\ t \in T), \qquad x, f \ge 0,
--   $$
--   where $P_h(t)$ is the set of simple $r$–$t$ paths of length at most $h$.
--
--   **Theorem 1.1 (Rooted guarantees).** There are an absolute constant $C > 0$ and two deterministic algorithms, each running in time polynomial jointly in the complete binary input and $1/\varepsilon$, such that on every strictly feasible planar rooted instance each returns, for every terminal $t$, a simple path $P_t : r \rightsquigarrow t$ with
--   $$
--   \ell(P_t) \le (1 + \varepsilon)h ,
--   $$
--   and the unions $F_1$, $F_2$ of their paths satisfy
--   $$
--   c(F_1) \le \frac{C D^2}{\varepsilon}\, \mathrm{OPT}_h = O\bigl(\varepsilon^{-1}\log^2(2k)\bigr)\, \mathrm{OPT}_h, \qquad c(F_2) \le \frac{C D^3}{\varepsilon}\, \mathrm{LP}_h = O\bigl(\varepsilon^{-1}\log^3(2k)\bigr)\, \mathrm{LP}_h .
--   $$
--
--   This is the rooted counterpart of the forest guarantee (Theorem 1.2): lengths are violated by a factor $1 + \varepsilon$ only, at polylogarithmic cost against both the integral optimum and the strict LP.
--
--   **Formalization Note** A rooted instance is an instance of the mission whose demands all have the form $(r, t)$; the terminal set is the set of targets. The algorithms are functions on all instances computed by Turing machines (`Turing.TM2ComputableInPolyTime`) on the binary encoding padded by $\lceil 1/\varepsilon \rceil$ symbols. $\mathrm{OPT}_h$ is compared through every strict tree $S$, and $\mathrm{LP}_h$ through every feasible point of the LP (a valid `RootData` on the same graph and root, with the instance's terminals and every bound equal to $h$).
--
--   Differences from the source:
--   - encoding: cost guarantees O(ε^{−1} log^2(2k)) OPT_h and O(ε^{−1} log^3(2k)) LP_h → one absolute constant C > 0, fixed before both machines and every instance, with c(F₁) ≤ C·D²/ε·c(S) and c(F₂) ≤ C·D³/ε·X(R), D = 1 + ⌈log₂ k⌉ (Dlog k); reason: log₂(2k) ≤ D ≤ 2 log₂(2k) for k ≥ 1, so C·D^j/ε and O(ε^{−1} log^j(2k)) are the same class; one constant for both halves is the larger of two
--   - generalization: k ≥ 1 terminals → any k ≥ 0 (every demand may be the root itself); reason: an empty terminal set is free (§3, p.4); the k ≥ 1 instances are a special case
--   - generalization: original root–terminal paths → simple paths (IsSPath) from r to each terminal; reason: a simple path is an original path; nonnegative lengths permit cycle erasure (§3, p.4)
--   - reading: deterministic algorithms … Both running times are polynomial jointly in the complete binary input and 1/ε → two functions alg₁, alg₂, each computed by a Turing machine (TM2) in time polynomial in the length of the binary instance padded by ⌈1/ε⌉ symbols (encIn); reason: the paper names no machine model; TM2 machines are deterministic, and the padding makes the input length the binary size plus 1/ε up to one; same convention as the published goal
--   - encoding: OPT_h; LP_h, the strict path-flow relaxation (1) → every strict tree S (StrictForest of the rooted demands); every valid RootData R on the same graph and root, with terminal set equal to the instance's and every bound b_t = h, with value R.X; reason: OPT_h is a minimum over finitely many arc sets; a valid RootData with these parameters is exactly a feasible point of (1) and P_h(t) is finite, so the LP minimum is attained
--   - encoding: planar rooted instance (G, r, T) with shared union F; strictly feasible instances → a valid Inst whose demands are all (r, t), terminals = distinct targets, one returned path per demand, F = union of the arcs of the returned paths; planarity of the simple underlying graph of all arcs; the hypothesis that all arcs form a strict tree; reason: Lean convention of the published mission; any union containing the paths costs at least as much; loops and parallel arcs are always drawable
--   - reading: k, the size of the terminal set T (§1, p.2) → k = number of distinct targets other than r; reason: §3, p.4 defines D = 1 + ⌈log₂ k⌉ after removing the root from the terminal set, and the proofs' constants are in that D; if r ∈ T the two counts differ by one, and log₂(2(k+1)) ≤ 2 log₂(2k) for k ≥ 1, so the O-classes agree
-- source:
--   Mahboub, Rahgoshay, Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar Graphs, STOC 2027 submission (manuscript sha256 5af18346c1fe696ca8ed57aa7736510e10e27188695bb15edcbe662315790dda), Theorem 1.1, p.2; model and LP (1), §1, p.2; D, §3, p.4; proofs: Integral part of theorem 1.1, p.8, LP part of theorem 1.1, p.9

import Mathlib
import Definitions.Def_LCPlanarSteiner_Inst
import Definitions.Def_LCPlanarSteiner_IsSPath
import Definitions.Def_LCPlanarSteiner_plen
import Definitions.Def_LCPlanarSteiner_pcost
import Definitions.Def_LCPlanarSteiner_StrictForest
import Definitions.Def_LCPlanarSteiner_RootData
import Definitions.Def_LCPlanarSteiner_underlying
import Definitions.Def_LCPlanarSteiner_Dlog
import Definitions.Def_LCPlanarSteiner_encIn
import Definitions.Def_LCPlanarSteiner_encPaths
import Definitions.Def_RobertsonSeymour1986_GM5_IsPlanar

namespace LCPlanarSteiner.Supplement

open LCPlanarSteiner

/-- **Theorem 1.1 (Rooted guarantees).**
Mahboub, Rahgoshay, *Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar
Graphs*, STOC 2027 submission (manuscript sha256 5af18346…), Theorem 1.1, p.2: "For planar rooted
directed Steiner tree with k ≥ 1 terminals, deterministic algorithms return original root–terminal
paths of length at most (1 + ε)h with cost guarantees, respectively, O(ε^{−1} log^2(2k)) OPT_h and
O(ε^{−1} log^3(2k)) LP_h. Both running times are polynomial jointly in the complete binary input and
1/ε." Model and LP (1): §1, p.2; `D = 1 + ⌈log₂ k⌉ after removing the root from the terminal set`:
§3, p.4; proofs: "Integral part of theorem 1.1", p.8, and "LP part of theorem 1.1", p.9.

A rooted instance is a valid instance `I` all of whose demands are `(r, t)` for one root `r`; its
terminal set is the set of targets, and `k` is the number of distinct targets other than `r`.
There are an absolute constant `C > 0` and two functions `alg₁`, `alg₂`, each computable by a Turing
machine in time polynomial in the length of `encIn I` (the binary instance padded by `⌈1/ε⌉`
symbols), such that for every rooted valid instance whose underlying graph is planar and in which
every terminal has an original path from `r` of length `≤ h`, each `alg_j I` lists one simple path
from `r` to `t_i` of length `≤ (1 + ε)h` per demand `(r, t_i)`, and the union `F_j` of its arcs
satisfies
1. `c(F₁) ≤ C · D² / ε · c(S)` for every strict tree `S` (so `c(F₁) ≤ C D² ε⁻¹ OPT_h`);
2. `c(F₂) ≤ C · D³ / ε · X(R)` for every feasible point `R` of the strict path LP (1), i.e. every
   valid rooted datum on the same graph and root whose terminals are exactly the instance's
   terminals, with every bound `b_t = h` (so `c(F₂) ≤ C D³ ε⁻¹ LP_h`),
where `D = 1 + ⌈log₂ k⌉`.

**Formalization Note.** The constant and both machines are fixed before the instance; TM2 is
deterministic. `log₂(2k) ≤ D ≤ 2 log₂(2k)` for `k ≥ 1`, so `C D^j / ε` is the printed
`O(ε^{−1} log^j(2k))`. `OPT_h` is compared through every strict tree `S` and `LP_h` through every
feasible point (finitely many simple paths, so the LP minimum is attained). A target equal to the
root is served by the empty path and does not count in `k`; `k = 0` is allowed (an empty terminal
set is free, p.4). `h = 0` is allowed (p.5). -/
theorem theorem_1_1 :
    ∃ C : ℚ, 0 < C ∧
    ∃ alg₁ alg₂ : Inst → List (List ℕ),
      Nonempty (Turing.TM2ComputableInPolyTime encIn encPaths alg₁) ∧
      Nonempty (Turing.TM2ComputableInPolyTime encIn encPaths alg₂) ∧
      ∀ (I : Inst) (r k : ℕ), I.Valid →
        (∀ d ∈ I.dem, d.1 = r) →
        k = ((I.dem.map Prod.snd).dedup.filter (fun t => t ≠ r)).length →
        RobertsonSeymour1986.GM5.IsPlanar (underlying I.net I.net.allArcs) →
        StrictForest I.net I.dem I.h I.net.allArcs →
        ((alg₁ I).length = I.dem.length ∧
          (∀ i < I.dem.length,
            IsSPath I.net r (I.dem.getD i (0, 0)).2 ((alg₁ I).getD i []) ∧
            plen I.net ((alg₁ I).getD i []) ≤ (1 + I.ε) * I.h) ∧
          ∀ S : Finset ℕ, StrictForest I.net I.dem I.h S →
            pcost I.net (alg₁ I).flatten.toFinset ≤
              C * (Dlog k : ℚ) ^ 2 / I.ε * pcost I.net S) ∧
        ((alg₂ I).length = I.dem.length ∧
          (∀ i < I.dem.length,
            IsSPath I.net r (I.dem.getD i (0, 0)).2 ((alg₂ I).getD i []) ∧
            plen I.net ((alg₂ I).getD i []) ≤ (1 + I.ε) * I.h) ∧
          ∀ R : RootData, R.net = I.net → R.root = r →
            (R.terms.map Prod.fst).toFinset = (I.dem.map Prod.snd).toFinset →
            (∀ τ ∈ R.terms, τ.2.1 = I.h) → R.Valid I.h →
            pcost I.net (alg₂ I).flatten.toFinset ≤
              C * (Dlog k : ℚ) ^ 3 / I.ε * R.X) := by sorry

end LCPlanarSteiner.Supplement

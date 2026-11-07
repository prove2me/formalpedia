-- Prove2me | Theorems.Thm_LCPlanarSteiner_lemma_4_5
-- name    : LCPlanarSteiner.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:07:30.028961+00:00
-- url     : https://prove2.me/theorems/ce4736e7-3b41-442f-a82b-80b83d4f52de
-- title:
--   Lemma 4.5 — the total-budget LP: size, junction feasibility, decomposition, and a root of value $\le 4C_{NE}D_r^2c(S)/(\varepsilon r)$
-- statement:
--   Let $G$ be a graph with $n$ vertices, $m$ arcs and nonnegative costs and lengths, $h > 0$, $0 < \varepsilon \le 1$, and $(s_i, t_i)$, $i \in [r]$, $r \ge 1$, nonself pairs. For a root $v$, consider the staged density LP with parameters (14) and constraints (15).
--
--   **Lemma 4.5.**
--   1. The LP has polynomial binary size: it has $Q + 1 \le 16n/\varepsilon + 4n + 1$ levels and at most $m + r + 2r(m+1)(16n/\varepsilon + 4n + 1)$ variables.
--   2. A junction $(H', v, I)$ with arm sums $\mathrm{dist}_{H'}(s_i, v) + \mathrm{dist}_{H'}(v, t_i) \le L_0$ for $i \in I$ gives a feasible point at root $v$ of value $c(H')/|I|$, its density.
--   3. Every feasible point decomposes, for each pair $i$, into finitely many (at most one per staged arc) paired simple original witnesses $s_i \rightsquigarrow v \rightsquigarrow t_i$ with masses summing to $y_i$, each with arm sum at most $U$, whose per-phase loads are dominated by $x$: in each phase the mass through any arc $e$ is at most $x_e$.
--   4. For every strict forest $S$ with planar underlying graph, some root trial has a feasible point of value at most
--   $$
--   \frac{4 C_{NE} D_r^2\, c(S)}{\varepsilon r},\qquad C_{NE} = 297 .
--   $$
--
--   The LP makes the junctions of Lemmas 4.3–4.4 searchable without guessing how the budget splits between the two arms.
--
--   **Formalization Note** At an optimal $S$ the bound in 4 is the paper's $4 C_{NE} D_r^2 \mathrm{OPT}^F_h/(\varepsilon r)$.
--
--   Differences from the source:
--   - reading: the LP has polynomial binary size → the number of levels is Q + 1 ≤ 16n/ε + 4n + 1 and the number of variables m + r + r·|staged arcs| is at most m + r + 2r(m+1)(16n/ε + 4n + 1); reason: the explicit counts behind the proof's "O(n/ε) levels and O(r(m+n)n/ε + m + r) variables"; the coefficients are input numbers and 0, ±1
--   - reading: polynomially supported paired original witnesses → for each pair, at most |staged arcs| weighted pairs of simple arms; reason: flow decomposition gives at most one path per staged arc; this is the polynomial support
--   - generalization: some root trial has value at most 4C_NE D_r² OPT^F_h/(εr) → for every strict forest S with planar underlying graph, some root v < n has a feasible point of value ≤ 4·297·D_r² c(S)/(εr); reason: at an optimal S (planar, since G is) this is the printed bound; the LP minimum is attained, so a feasible point of value ≤ K is a trial of value ≤ K
--   - encoding: staged flows, "when permitted", per-phase loads → flows on an explicit finite set of staged arcs with j + q_e ≤ Q; masses through each arc of G per phase ≤ x_e; rational points; reason: Lean convention, same LP
-- source:
--   Mahboub, Rahgoshay, Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar Graphs, STOC 2027 submission (manuscript sha256 5af18346c1fe696ca8ed57aa7736510e10e27188695bb15edcbe662315790dda), Lemma 4.5 and its proof, pp.14–15; displays (14)–(15), p.14

import Mathlib
import Definitions.Def_LCPlanarSteiner_IsSPath
import Definitions.Def_LCPlanarSteiner_plen
import Definitions.Def_LCPlanarSteiner_pcost
import Definitions.Def_LCPlanarSteiner_ArmsLE
import Definitions.Def_LCPlanarSteiner_Dlog
import Definitions.Def_LCPlanarSteiner_StrictForest
import Definitions.Def_LCPlanarSteiner_underlying
import Definitions.Def_LCPlanarSteiner_LPFeasible
import Definitions.Def_RobertsonSeymour1986_GM5_IsPlanar

namespace LCPlanarSteiner

/-- **Lemma 4.5 (the total-budget LP).**
Mahboub, Rahgoshay, *Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar
Graphs*, STOC 2027 submission (manuscript sha256 5af18346…), Lemma 4.5, pp.14–15: "The LP has polynomial binary size. A junction with arm sums at most L₀
gives a feasible point of its density. Every feasible point decomposes into polynomially supported
paired original witnesses of mass y_i, arm sum at most U, and per-phase loads dominated by x. Some
root trial has value at most 4C_NE D_r² OPT^F_h/(εr)." Proof, p.15: "There are O(n/ε) levels and
O(r(m+n)n/ε + m + r) variables"; `C_NE = 297` (Lemma 4.3).

For a well-formed graph, `h > 0`, `0 < ε ≤ 1` and `r ≥ 1` nonself pairs of vertices:
1. (size) the number of levels is `Q + 1 ≤ 16n/ε + 4n + 1`, and the number of variables
   `m + r + r·|staged arcs|` is at most `m + r + 2r(m + 1)(16n/ε + 4n + 1)`;
2. (junctions are feasible) for every junction `(H′, v, I)`, `v < n`, `I ⊆ [r]` nonempty, with arm
   sums `dist_{H′}(s_i, v) + dist_{H′}(v, t_i) ≤ L₀` (`i ∈ I`), the LP at root `v` has a feasible point
   of value `c(H′)/|I|`;
3. (decomposition) every feasible point at a root `v` decomposes, for each pair `i`, into at most
   `|staged arcs|` weighted pairs of simple paths `s_i ⇝ v` and `v ⇝ t_i` with masses `≥ 0` summing
   to `y_i`, each with arm sum `≤ U`, such that in each phase the mass through any arc `e` of `G` is
   at most `x_e`;
4. (some root is cheap) for every strict forest `S` with planar underlying graph, some root `v < n`
   has a feasible point of value at most `4 · 297 · D_r² c(S)/(εr)`.

**Formalization Note.** "Polynomial binary size" is the explicit count of levels and variables
from the proof; the support bound `|staged arcs|` is the "polynomially supported". `OPT^F_h` (the
optimum for these `r` pairs) is replaced by `c(S)` for every planar strict forest `S`; at an
optimal `S` this is the printed bound. "Some root trial has value at most K" is the existence of a
feasible point of value `≤ K` (the LP minimum is attained). -/
theorem lemma_4_5 (G : Net) (hG : G.WF) (h ε : ℚ) (hh : 0 < h) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (dem : List (ℕ × ℕ)) (hr : dem ≠ []) (hdem : ∀ d ∈ dem, d.1 < G.n ∧ d.2 < G.n)
    (hself : ∀ d ∈ dem, d.1 ≠ d.2) :
    ((lpQ G ε h + 1 : ℕ) : ℚ) ≤ 16 * G.n / ε + 4 * G.n + 1 ∧
    ((G.arcs.length + dem.length + dem.length * (stagedArcs G ε h).card : ℕ) : ℚ) ≤
      G.arcs.length + dem.length +
        2 * dem.length * (G.arcs.length + 1) * (16 * G.n / ε + 4 * G.n + 1) ∧
    (∀ (H' : Finset ℕ) (v : ℕ) (I : Finset ℕ), v < G.n → I.Nonempty →
      (∀ i ∈ I, i < dem.length) →
      (∀ i ∈ I, ArmsLE G H' v (dem.getD i (0, 0)).1 (dem.getD i (0, 0)).2 (lpL0 ε h)) →
      ∃ (x y : ℕ → ℚ) (f : ℕ → ℕ × ℕ × ℕ → ℚ), LPFeasible G dem v ε h x y f ∧
        lpValue G x = pcost G H' / I.card) ∧
    (∀ (v : ℕ) (x y : ℕ → ℚ) (f : ℕ → ℕ × ℕ × ℕ → ℚ), LPFeasible G dem v ε h x y f →
      ∃ dec : ℕ → List (List ℕ × List ℕ × ℚ), ∀ i < dem.length,
        (dec i).length ≤ (stagedArcs G ε h).card ∧
        ((dec i).map fun c => c.2.2).sum = y i ∧
        (∀ c ∈ dec i, 0 ≤ c.2.2 ∧ IsSPath G (dem.getD i (0, 0)).1 v c.1 ∧
          IsSPath G v (dem.getD i (0, 0)).2 c.2.1 ∧ plen G c.1 + plen G c.2.1 ≤ lpU ε h) ∧
        (∀ e < G.arcs.length, (((dec i).filter fun c => decide (e ∈ c.1)).map fun c => c.2.2).sum ≤ x e) ∧
        (∀ e < G.arcs.length, (((dec i).filter fun c => decide (e ∈ c.2.1)).map fun c => c.2.2).sum ≤ x e)) ∧
    (∀ S : Finset ℕ, StrictForest G dem h S →
      RobertsonSeymour1986.GM5.IsPlanar (underlying G S) →
      ∃ v < G.n, ∃ (x y : ℕ → ℚ) (f : ℕ → ℕ × ℕ × ℕ → ℚ), LPFeasible G dem v ε h x y f ∧
        lpValue G x ≤ 4 * 297 * (Dlog dem.length : ℚ) ^ 2 * pcost G S / (ε * dem.length)) := by sorry

end LCPlanarSteiner

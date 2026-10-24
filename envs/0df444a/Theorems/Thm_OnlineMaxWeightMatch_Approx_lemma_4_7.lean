-- Prove2me | Theorems.Thm_OnlineMaxWeightMatch_Approx_lemma_4_7
-- name    : OnlineMaxWeightMatch.Approx.lemma_4_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:51:34.008323+00:00
-- url     : https://prove2.me/theorems/92fdb873-4ff2-442e-8da5-3d1d692ca047
-- title:
--   Lemma 4.7: Pr[i1 ≠ i | A_t] ≥ 1 − 4c for late edges
-- statement:
--   **Standing setting (§4).** $I$ is a RideHail instance with bins $i\in\iota$ (a finite set) and balls $t=1,\dots,n$, arrival probabilities $p_t\in[0,1]$ and weights $w_{i,t}\ge 0$. The vector $x=(x_{i,t})$ is a feasible solution of LP-Match (constraints (9)–(12)) that satisfies Constraint (10) with equality, $\sum_i x_{i,t}=p_t$ for every ball $t$ (the paper's standing assumption, guaranteed by the dummy bins of Line 2 of Algorithm 1). Algorithm 1 (Lines 3–13) is run on $x$ with $c=0.01$; $\Pr$ is the probability over its randomness (arrivals, first picks, acceptance coins, second picks).
--
--   For every late edge $(i,t)$ with $p_t>0$, the bin $i_1$ picked in Line 5 at time $t$ satisfies
--
--   $$
--   \Pr\big[i_1\neq i\ \big|\ A_t\big]\ \ge\ 1-4c,
--   $$
--
--   where $A_t$ is the event that ball $t$ arrives.
--
--   This is where Constraint (11) of LP-Match enters: a late ball picks the bin for which it is late with probability at most $4c$, so its second pick is rarely a re-draw of a bin already known to be occupied.
--
--   **Formalization Note** The hypothesis $p_t>0$ makes $A_t$ an event of positive probability; on a null event Lean's conditional measure is $0$. The event $i_1\ne i$ is the complement of $\{i_1=i\}$.
-- source:
--   Papadimitriou, Pollner, Saberi & Wajc, Online Stochastic Max-Weight Bipartite Matching: Beyond Prophet Inequalities, arXiv:2102.10261v3, p. 14, Lemma 4.7

import Mathlib
import Definitions.Def_OnlineMaxWeightMatch_Approx_Analysis

open MeasureTheory ProbabilityTheory

namespace OnlineMaxWeightMatch.Approx

/-- Lemma 4.7. For any late edge `(i, t)` (with `p_t > 0`, so that `A_t` has positive
probability), the bin `i_1` picked in Line 5 at time `t` satisfies
`Pr[i_1 ≠ i | A_t] ≥ 1 - 4c`. -/
theorem lemma_4_7 {ι : Type*} [Fintype ι] {n : ℕ} (I : RideHailInstance ι n)
    (x : ι → Fin n → ℝ) (hx : LPFeasible I x) (htight : ∀ t, ∑ i, x i t = I.p t)
    (i : ι) (t : Fin n) (hlate : IsLate x i t) (hp : 0 < I.p t) :
    1 - 4 * c ≤ (algMeasure I x)[|arrivalSet t].real ((firstPickSet t i)ᶜ) := by sorry

end OnlineMaxWeightMatch.Approx

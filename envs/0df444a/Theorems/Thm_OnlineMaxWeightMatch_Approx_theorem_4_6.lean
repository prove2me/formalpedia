-- Prove2me | Theorems.Thm_OnlineMaxWeightMatch_Approx_theorem_4_6
-- name    : OnlineMaxWeightMatch.Approx.theorem_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:52:01.159761+00:00
-- url     : https://prove2.me/theorems/7cd2304d-9765-40b1-9c6c-ac09a5e0b02f
-- title:
--   Theorem 4.6: late edges gain Pr[(i,t) ∈ M2] ≥ x_{i,t} · 4c from the second pick
-- statement:
--   **Standing setting (§4).** $I$ is a RideHail instance with bins $i\in\iota$ (a finite set) and balls $t=1,\dots,n$, arrival probabilities $p_t\in[0,1]$ and weights $w_{i,t}\ge 0$. The vector $x=(x_{i,t})$ is a feasible solution of LP-Match (constraints (9)–(12)) that satisfies Constraint (10) with equality, $\sum_i x_{i,t}=p_t$ for every ball $t$ (the paper's standing assumption, guaranteed by the dummy bins of Line 2 of Algorithm 1). Algorithm 1 (Lines 3–13) is run on $x$ with $c=0.01$; $\Pr$ is the probability over its randomness (arrivals, first picks, acceptance coins, second picks).
--
--   Let $M_2$ be the set of edges added in Line 12 (second picks). For every late edge $(i,t)$,
--
--   $$
--   \Pr[(i,t)\in M_2]\ \ge\ x_{i,t}\cdot 4c.
--   $$
--
--   The second pick thus adds a constant fraction $4c$ of the LP mass to every late edge, which is exactly what late edges lack after the first pick (Lemma 4.4).
-- source:
--   Papadimitriou, Pollner, Saberi & Wajc, Online Stochastic Max-Weight Bipartite Matching: Beyond Prophet Inequalities, arXiv:2102.10261v3, p. 13, Theorem 4.6 (proof pp. 16–17)

import Mathlib
import Definitions.Def_OnlineMaxWeightMatch_Approx_Analysis

open MeasureTheory ProbabilityTheory

namespace OnlineMaxWeightMatch.Approx

/-- Theorem 4.6. For any late edge `(i, t)`, `Pr[(i, t) ∈ M2] ≥ x_{i,t} · 4c`. -/
theorem theorem_4_6 {ι : Type*} [Fintype ι] {n : ℕ} (I : RideHailInstance ι n)
    (x : ι → Fin n → ℝ) (hx : LPFeasible I x) (htight : ∀ t, ∑ i, x i t = I.p t)
    (i : ι) (t : Fin n) (hlate : IsLate x i t) :
    x i t * (4 * c) ≤ (algMeasure I x).real {ω | (i, t) ∈ M2 x ω} := by sorry

end OnlineMaxWeightMatch.Approx

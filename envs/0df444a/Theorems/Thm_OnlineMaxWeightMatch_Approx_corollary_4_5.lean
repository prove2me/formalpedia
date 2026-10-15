-- Prove2me | Theorems.Thm_OnlineMaxWeightMatch_Approx_corollary_4_5
-- name    : OnlineMaxWeightMatch.Approx.corollary_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:51:59.775981+00:00
-- url     : https://prove2.me/theorems/1061311a-ecbd-4685-b22c-605aeab56547
-- title:
--   Corollary 4.5: bounds on the vacancy probability Pr[V_{i,t}]
-- statement:
--   **Standing setting (§4).** $I$ is a RideHail instance with bins $i\in\iota$ (a finite set) and balls $t=1,\dots,n$, arrival probabilities $p_t\in[0,1]$ and weights $w_{i,t}\ge 0$. The vector $x=(x_{i,t})$ is a feasible solution of LP-Match (constraints (9)–(12)) that satisfies Constraint (10) with equality, $\sum_i x_{i,t}=p_t$ for every ball $t$ (the paper's standing assumption, guaranteed by the dummy bins of Line 2 of Algorithm 1). Algorithm 1 (Lines 3–13) is run on $x$ with $c=0.01$; $\Pr$ is the probability over its randomness (arrivals, first picks, acceptance coins, second picks).
--
--   Let $V_{i,t}$ be the event that bin $i$ is vacant at time $t$ (before ball $t$ is processed). Then:
--   1. for every edge $(i,t)$, $\Pr[V_{i,t}]\ge 1/2-3c$;
--   2. for every late edge $(i,t)$, $\Pr[V_{i,t}]\le 1/2+c$;
--   3. for every early edge $(i,t)$,
--   $$
--   \Pr[V_{i,t}]=1-\sum_{t'<t}x_{i,t'}\cdot(1/2+c).
--   $$
--
--   These bounds are extracted from the proof of Lemma 4.4 and are used throughout the analysis of the second pick.
-- source:
--   Papadimitriou, Pollner, Saberi & Wajc, Online Stochastic Max-Weight Bipartite Matching: Beyond Prophet Inequalities, arXiv:2102.10261v3, p. 13, Corollary 4.5

import Mathlib
import Definitions.Def_OnlineMaxWeightMatch_Approx_Analysis

open MeasureTheory ProbabilityTheory

namespace OnlineMaxWeightMatch.Approx

/-- Corollary 4.5. For every edge `(i, t)`, `Pr[V_{i,t}] ≥ 1/2 - 3c`; for late `(i, t)`,
`Pr[V_{i,t}] ≤ 1/2 + c`; for early `(i, t)`, `Pr[V_{i,t}] = 1 - Σ_{t'<t} x_{i,t'} · (1/2 + c)`. -/
theorem corollary_4_5 {ι : Type*} [Fintype ι] {n : ℕ} (I : RideHailInstance ι n)
    (x : ι → Fin n → ℝ) (hx : LPFeasible I x) (htight : ∀ t, ∑ i, x i t = I.p t)
    :
    (∀ i t, 1 / 2 - 3 * c ≤ (algMeasure I x).real (vacantSet x i t)) ∧
    (∀ i t, IsLate x i t → (algMeasure I x).real (vacantSet x i t) ≤ 1 / 2 + c) ∧
    (∀ i t, IsEarly x i t →
      (algMeasure I x).real (vacantSet x i t) = 1 - cumX x i t * (1 / 2 + c)) := by sorry

end OnlineMaxWeightMatch.Approx

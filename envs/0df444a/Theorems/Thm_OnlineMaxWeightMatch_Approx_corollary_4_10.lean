-- Prove2me | Theorems.Thm_OnlineMaxWeightMatch_Approx_corollary_4_10
-- name    : OnlineMaxWeightMatch.Approx.corollary_4_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:52:10.016996+00:00
-- url     : https://prove2.me/theorems/e0759e6d-a0a6-47fe-ad90-8a4c7f45c8ad
-- title:
--   Corollary 4.10: Cov(O^E_{i,t}, O^E_{j,t}) ≤ 0
-- statement:
--   **Standing setting (§4).** $I$ is a RideHail instance with bins $i\in\iota$ (a finite set) and balls $t=1,\dots,n$, arrival probabilities $p_t\in[0,1]$ and weights $w_{i,t}\ge 0$. The vector $x=(x_{i,t})$ is a feasible solution of LP-Match (constraints (9)–(12)) that satisfies Constraint (10) with equality, $\sum_i x_{i,t}=p_t$ for every ball $t$ (the paper's standing assumption, guaranteed by the dummy bins of Line 2 of Algorithm 1). Algorithm 1 (Lines 3–13) is run on $x$ with $c=0.01$; $\Pr$ is the probability over its randomness (arrivals, first picks, acceptance coins, second picks).
--
--   For every ball $t$ and bins $i\neq j$,
--
--   $$
--   \operatorname{Cov}\big(O^E_{i,t},\,O^E_{j,t}\big)\ \le\ 0,
--   $$
--
--   where $O^E_{i,t}$ indicates that bin $i$ has been matched along an early edge before $t$ arrives. It follows from Lemma 4.9 and Proposition 2.8 and is the main input of Lemma 4.8.
-- source:
--   Papadimitriou, Pollner, Saberi & Wajc, Online Stochastic Max-Weight Bipartite Matching: Beyond Prophet Inequalities, arXiv:2102.10261v3, p. 15, Corollary 4.10

import Mathlib
import Definitions.Def_OnlineMaxWeightMatch_Approx_Analysis

open MeasureTheory ProbabilityTheory

namespace OnlineMaxWeightMatch.Approx

/-- Corollary 4.10. For any time `t` and bins `i ≠ j`, `Cov(O^E_{i,t}, O^E_{j,t}) ≤ 0`. -/
theorem corollary_4_10 {ι : Type*} [Fintype ι] {n : ℕ} (I : RideHailInstance ι n)
    (x : ι → Fin n → ℝ) (hx : LPFeasible I x) (htight : ∀ t, ∑ i, x i t = I.p t)
    (t : Fin n) {i j : ι} (hij : i ≠ j) :
    cov[occupancyEarly x i t, occupancyEarly x j t; algMeasure I x] ≤ 0 := by sorry

end OnlineMaxWeightMatch.Approx

-- Prove2me | Theorems.Thm_OnlineMaxWeightMatch_Approx_lemma_4_8
-- name    : OnlineMaxWeightMatch.Approx.lemma_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:52:00.271913+00:00
-- url     : https://prove2.me/theorems/29c1ca87-fbb2-453c-b76b-e554e72728ac
-- title:
--   Lemma 4.8: Cov(V_{i,t}, V_{j,t}) ≤ 12c
-- statement:
--   **Standing setting (§4).** $I$ is a RideHail instance with bins $i\in\iota$ (a finite set) and balls $t=1,\dots,n$, arrival probabilities $p_t\in[0,1]$ and weights $w_{i,t}\ge 0$. The vector $x=(x_{i,t})$ is a feasible solution of LP-Match (constraints (9)–(12)) that satisfies Constraint (10) with equality, $\sum_i x_{i,t}=p_t$ for every ball $t$ (the paper's standing assumption, guaranteed by the dummy bins of Line 2 of Algorithm 1). Algorithm 1 (Lines 3–13) is run on $x$ with $c=0.01$; $\Pr$ is the probability over its randomness (arrivals, first picks, acceptance coins, second picks).
--
--   For every ball $t$ and bins $i\neq j$, the vacancy indicators at time $t$ satisfy
--
--   $$
--   \operatorname{Cov}\big(V_{i,t},\,V_{j,t}\big)\ \le\ 12c.
--   $$
--
--   This is the crux of the analysis: matched statuses of different bins may be positively correlated, but only weakly, which is what lets the second pick of a ball succeed with non-negligible probability.
-- source:
--   Papadimitriou, Pollner, Saberi & Wajc, Online Stochastic Max-Weight Bipartite Matching: Beyond Prophet Inequalities, arXiv:2102.10261v3, p. 14, Lemma 4.8

import Mathlib
import Definitions.Def_OnlineMaxWeightMatch_Approx_Analysis

open MeasureTheory ProbabilityTheory

namespace OnlineMaxWeightMatch.Approx

/-- Lemma 4.8. For any time `t` and bins `i ≠ j`, `Cov(V_{i,t}, V_{j,t}) ≤ 12c`. -/
theorem lemma_4_8 {ι : Type*} [Fintype ι] {n : ℕ} (I : RideHailInstance ι n)
    (x : ι → Fin n → ℝ) (hx : LPFeasible I x) (htight : ∀ t, ∑ i, x i t = I.p t)
    (t : Fin n) {i j : ι} (hij : i ≠ j) :
    cov[vacancy x i t, vacancy x j t; algMeasure I x] ≤ 12 * c := by sorry

end OnlineMaxWeightMatch.Approx

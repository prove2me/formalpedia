-- Prove2me | Theorems.Thm_LostSalesConstantOrder_LargeLeadTime_lemma_9_law
-- name    : LostSalesConstantOrder.LargeLeadTime.lemma_9_law
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:04:19.049238+00:00
-- url     : https://prove2.me/theorems/54614f27-86ef-4afc-a625-ac35d028cc31
-- title:
--   Lemma 9 (law): $i^r_k$ has the distribution of $\min(k,i^r_\infty)$
-- statement:
--   Let $D_1,D_2,\dots$ be i.i.d. with law $\mathcal D$ (finite third moment, not deterministic), $r\in[0,\mathbb E[D])$, and $I^r_{1,\infty}$ a copy of $I^r_\infty$ independent of the demands. For all integers $j,k\ge0$, the last maximizer $i^r_k$ of $W^r_k=\max_{j\le k}(jr-\sum_{i=1}^jD_i+\delta_{j,k}I^r_{1,\infty})$ satisfies
--   $$
--   \mathbb P(i^r_k=j)=\mathbb P\big(\min(k,i^r_\infty)=j\big).
--   $$
--
--   It lets every expectation involving $i^r_k$ in Theorem 8 be bounded through the single random variable $i^r_\infty$.
--
--   **Formalization Note** The left probability is under the product of the law of $I^r_\infty$ and the demand law.
-- source:
--   Goldberg, Katz-Rogozhnikov, Lu, Sharma & Squillante, Asymptotic Optimality of Constant-Order Policies for Lost Sales Inventory Models with Large Lead Times, arXiv:1211.4063v2, p. 10, Lemma 9 (first sentence)

import Definitions.Def_LostSalesConstantOrder_LargeLeadTime_RandomWalk

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace LostSalesConstantOrder.LargeLeadTime

/-- Lemma 9, p. 10 (first part): for `r ∈ [0, E[D])` and integers `j, k ≥ 0`, `i^r_k` has the
distribution of `min(k, i^r_∞)`: `P(i^r_k = j) = P(min(k, i^r_∞) = j)`. -/
theorem lemma_9_law (P : CappedBaseStock.DemandLaw) (prm : CappedBaseStock.Parameters)
    (h3 : FiniteThirdMoment P) (hnd : NonDeterministic P)
    (r : ℝ≥0) (hr : (r : ℝ) < CappedBaseStock.mean P) (k j : ℕ) :
    ((lawSupWalk P r).prod (CappedBaseStock.demandPathLaw P)) {p | ik r k p.1 p.2 = j} =
      CappedBaseStock.demandPathLaw P {d | min k (argmaxWalk r d) = j} := by sorry

end LostSalesConstantOrder.LargeLeadTime

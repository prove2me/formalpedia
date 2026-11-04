-- Prove2me | Theorems.Thm_LostSalesExpGap_ConstOrder_best_constant_exists
-- name    : LostSalesExpGap.ConstOrder.best_constant_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:11:38.445993+00:00
-- url     : https://prove2.me/theorems/5ec15119-7ad4-4326-b9ac-955419b90cc9
-- title:
--   Sec. 2.2, p. 7 — an optimal constant order exists, optimal levels are bounded away from E[D], r∞ < E[D]
-- statement:
--   In the lost-sales model (i.i.d. nonnegative demand $D$ with finite mean and strictly positive variance, lead time $L\ge1$, costs $h,p>0$, empty initial state), let $C(\pi_r)$ be the long-run average cost of the policy ordering $r$ every period, and let
--   $$
--   A=\operatorname*{argmin}_{0\le r\le\mathbb E[D]}C(\pi_r),\qquad r_\infty=\inf A .
--   $$
--   Then:
--   1. $A$ is nonempty;
--   2. $A$ is bounded away from $\mathbb E[D]$: there is $\delta>0$ with $r\le\mathbb E[D]-\delta$ for all $r\in A$;
--   3. $r_\infty\in A$;
--   4. in particular $r_\infty<\mathbb E[D]$.
--
--   This makes the best constant-order policy $\pi_{r_\infty}$ well defined and places it in the regime where formula (3) applies.
--
--   **Formalization Note** Costs are compared in $[0,\infty]$. Strictly positive variance is encoded as "the demand law is not a point mass" (`NonDeterministic`). Items 3 and 4 make explicit what the paper uses when it writes $r_\infty\in\operatorname{argmin}$ and $r_\infty<\mathbb E[D]$.
-- source:
--   Xin, Goldberg, Optimality gap of constant-order policies decays exponentially in the lead time for lost sales models, arXiv:1409.1499v2, Sec. 2.2, p. 7

import Mathlib
import Definitions.Def_LostSalesExpGap_ConstOrder_ConstantOrder

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace LostSalesExpGap.ConstOrder

/-- Sec. 2.2, p. 7: an optimal constant-order level exists, the set of optimal levels is bounded
away from `E[D]`, and its infimum `r∞` is itself optimal, so `r∞ < E[D]`. -/
theorem best_constant_exists (P : CappedBaseStock.DemandLaw) (c : CappedBaseStock.Parameters)
    (hP : LostSalesConstantOrder.LargeLeadTime.NonDeterministic P) :
    (argminConst P c).Nonempty ∧
      (∃ δ : ℝ, 0 < δ ∧ ∀ r ∈ argminConst P c, r ≤ CappedBaseStock.mean P - δ) ∧
      rInf P c ∈ argminConst P c ∧
      rInf P c < CappedBaseStock.mean P := by sorry

end LostSalesExpGap.ConstOrder

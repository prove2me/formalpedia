-- Prove2me | Theorems.Thm_LostSalesConstantOrder_LargeLeadTime_lemma_10
-- name    : LostSalesConstantOrder.LargeLeadTime.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:05:21.884437+00:00
-- url     : https://prove2.me/theorems/e7ab1fea-777f-4817-97d9-a492f4b42efb
-- title:
--   Lemma 10: $\mathbb E[D]-r^*\ge\frac12\sigma m^{-1/2}$ once $L\ge8(\sigma^{-1}Q+1)m^{3/2}$
-- statement:
--   In the lost-sales system with lead time $L$, costs $h,c>0$ and demand law $\mathcal D$ (finite third moment, not deterministic), let $\sigma$ be the standard deviation of the demand, $Q$ its $c/(c+h)$ quantile, $\zeta$ its skewness and $m=\lceil(26(3\zeta+c(h\sigma)^{-1}\mathbb E[D]+1))^2\rceil$. Let $(\mathbf x^*,\mathcal I^*)$ be any solution of problem (4) and $r^*=L^{-1}\sum_{i=1}^Lx^*_i$. If $L\ge8(\sigma^{-1}Q+1)m^{3/2}$, then
--   $$
--   \mathbb E[D]-r^*\ \ge\ \tfrac12\,\sigma\,m^{-1/2}.
--   $$
--
--   It keeps $r^*$ uniformly away from $\mathbb E[D]$, which bounds $\Theta_{r^*}^{-3}$ in Theorem 8 independently of $L$.
-- source:
--   Goldberg, Katz-Rogozhnikov, Lu, Sharma & Squillante, Asymptotic Optimality of Constant-Order Policies for Lost Sales Inventory Models with Large Lead Times, arXiv:1211.4063v2, p. 11, Lemma 10

import Definitions.Def_LostSalesConstantOrder_LargeLeadTime_ConstantOrder

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace LostSalesConstantOrder.LargeLeadTime

/-- Lemma 10, p. 11: if `L ≥ 8(σ⁻¹Q + 1)m^{3/2}`, then for every solution `(x*, 𝓘*)` of (4),
`E[D] − r* ≥ ½σm^{−1/2}`, where `r* = L⁻¹ Σ x*_i`. -/
theorem lemma_10 (P : CappedBaseStock.DemandLaw) (prm : CappedBaseStock.Parameters)
    (h3 : FiniteThirdMoment P) (hnd : NonDeterministic P)
    (hL : 8 * ((Qlevel P prm : ℝ) / sigma P + 1) * (mConst P prm : ℝ) ^ ((3 : ℝ) / 2) ≤ prm.L)
    (x : Fin prm.L → ℝ≥0) (I : ℝ≥0) (hmin : IsWindowMinimizer P prm x I) :
    1 / 2 * sigma P * (mConst P prm : ℝ) ^ (-(1 / 2 : ℝ)) ≤
      CappedBaseStock.mean P - rStar x := by sorry

end LostSalesConstantOrder.LargeLeadTime

-- Prove2me | Theorems.Thm_LostSalesOrderUpTo_Asymptotic_newsvendor_optimal
-- name    : LostSalesOrderUpTo.Asymptotic.newsvendor_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T08:49:28.126215+00:00
-- url     : https://prove2.me/theorems/3689056b-0f7e-490d-8743-6651e43f0cd8
-- title:
--   Newsvendor formula attains backorder optimum
-- statement:
--   Let $\mathbf D$ have a nonnegative probability distribution with finite mean, and let $h,b>0$. Write $F(y)=\Pr(\mathbf D\le y)$ and define
--
--   $$S^{\mathcal B*}(h,b)=\inf\left\{y\ge0:F(y)\ge\frac{b}{b+h}\right\}.$$
--
--   This level attains the optimal order-up-to cost:
--
--   $$C^{\mathcal B,S^{\mathcal B*}(h,b)}(h,b)=C^{\mathcal B*}(h,b).$$
--
--   The result identifies the explicit stock level used in the lost-sales policy.
-- source:
--   Huh, Janakiraman, Muckstadt & Rusmevichientong, Asymptotic Optimality of Order-up-to Policies in Lost Sales Inventory Systems, working paper, December 4, 2006 (preprint of Management Science 55(3), 2009, DOI 10.1287/mnsc.1080.0945), p. 12, §4, proof of Theorem 6 (newsvendor formula)

import Definitions.Def_LostSalesOrderUpTo_Asymptotic_Backorder

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators

namespace LostSalesOrderUpTo.Asymptotic

/-- The newsvendor formula attains the best backorder order-up-to cost. -/
theorem newsvendor_optimal (μ : Measure ℝ≥0) [IsProbabilityMeasure μ]
    (h b : ℝ) (hh : 0 < h) (hb : 0 < b)
    (hmean : Integrable (fun d : ℝ≥0 => (d : ℝ)) μ) :
    backorderCost μ h b (newsvendorLevel μ h b) =
      backorderOptimalCost μ h b := by sorry

end LostSalesOrderUpTo.Asymptotic

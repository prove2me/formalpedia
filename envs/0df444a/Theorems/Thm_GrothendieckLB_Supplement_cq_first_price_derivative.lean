-- Prove2me | Theorems.Thm_GrothendieckLB_Supplement_cq_first_price_derivative
-- name    : GrothendieckLB.Supplement.cq_first_price_derivative
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-23T21:34:25.477803+00:00
-- url     : https://prove2.me/theorems/2f8351d9-16fb-47ee-811b-1be06a09a825
-- title:
--   First Price derivative of the cubic–quintic correlation
-- statement:
--   Differentiating the cubic–quintic threshold correlation produces two mixed Gaussian integrals. One comes from varying the covariance of the first coordinate. The other comes from varying the reflected spatial covariance and has the opposite sign. The formula holds for its holomorphic extension throughout the open unit disk.
-- source:
--   Independent Price differentiation and rational interval certificate for Saha et al., arXiv:2608.11158v2. The density identity is Prove2Me bb4bfdfc-4dcc-425d-8a98-1b646de8d12b.

import Mathlib
import Definitions.Def_GrothendieckLB_Supplement_cqCorr
import Definitions.Def_GrothendieckLB_Supplement_cqPriceMajorant
import Definitions.Def_GrothendieckLB_Supplement_cqPriceKernels

namespace GrothendieckLB.Supplement

theorem cq_first_price_derivative (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (Metric.ball 0 1))
    (hreal : ∀ t : ℝ, |t|<1 → F (t:ℂ)=(cqCorr 0.136419125 0.34101124 0.05276111 t:ℂ))
    (z : ℂ) (hz : ‖z‖<1) :
    HasDerivAt F (deriv (CQPrice.eval CQPrice.rho) z * CQPrice.partialTerm z 1 0 - CQPrice.partialTerm z 0 1) z := by sorry

end GrothendieckLB.Supplement

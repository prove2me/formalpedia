-- Prove2me | Theorems.Thm_GrothendieckLB_Supplement_cq_threshold_integral_derivative
-- name    : GrothendieckLB.Supplement.cq_threshold_integral_derivative
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T22:02:21.596616+00:00
-- url     : https://prove2.me/theorems/00234486-b417-49a4-9a4b-7f47c7839950
-- title:
--   Derivative of the cubic–quintic shifted threshold integral
-- statement:
--   Varying the parameter in the cubic–quintic Gaussian expectation differentiates the polynomial covariance and the reflected spatial covariance. The two resulting terms are exactly the zeroth-order Fourier moments weighted by the indicated cubic derivatives.
-- source:
--   Independent Price differentiation and rational interval certificate for Saha et al., arXiv:2608.11158v2. The density identity is Prove2Me bb4bfdfc-4dcc-425d-8a98-1b646de8d12b.

import Definitions.Def_GrothendieckLB_Supplement_cqPriceKernels
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_GrothendieckLB_Supplement_cqThresholdKernel

namespace GrothendieckLB.Supplement

theorem cq_threshold_integral_derivative (z : ℂ) (hz : ‖z‖<1) :
    HasDerivAt CQThreshold.H
      (deriv (CQPrice.eval CQPrice.rho) z * CQPrice.partialTerm z 1 0 - CQPrice.partialTerm z 0 1) z := by sorry

end GrothendieckLB.Supplement

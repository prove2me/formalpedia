-- Prove2me | Theorems.Thm_GrothendieckLB_Supplement_cq_mixed_price_derivative
-- name    : GrothendieckLB.Supplement.cq_mixed_price_derivative
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-23T21:35:45.013373+00:00
-- url     : https://prove2.me/theorems/360f5c12-a953-44b9-a47a-6aae8983e04f
-- title:
--   Differentiation of mixed Gaussian threshold integrals
-- statement:
--   An interior mixed Gaussian integral of positive order below five has two derivative terms. Differentiating its Fourier covariance raises the parameter order, and differentiating its spatial Gaussian raises the common spatial order after two integrations by parts.
-- source:
--   Independent Price differentiation and rational interval certificate for Saha et al., arXiv:2608.11158v2. The density identity is Prove2Me bb4bfdfc-4dcc-425d-8a98-1b646de8d12b.

import Definitions.Def_GrothendieckLB_Supplement_cqPriceKernels
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace GrothendieckLB.Supplement

theorem cq_mixed_price_derivative (p a : ℕ) (hpos : 0<p+a) (hlt : p+a<5) (z : ℂ) (hz : ‖z‖<1) :
    HasDerivAt (fun w => CQPrice.partialTerm w p a)
      (deriv (CQPrice.eval CQPrice.rho) z * CQPrice.partialTerm z (p+1) a - CQPrice.partialTerm z p (a+1)) z := by sorry

end GrothendieckLB.Supplement

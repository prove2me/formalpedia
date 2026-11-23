-- Prove2me | Theorems.Thm_GrothendieckLB_Supplement_cq_price_partial_gaussian_bound
-- name    : GrothendieckLB.Supplement.cq_price_partial_gaussian_bound
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-23T21:17:06.539402+00:00
-- url     : https://prove2.me/theorems/129ac1b4-1df2-44cd-9086-3d846ec14f06
-- title:
--   Absolute moment bound for a mixed Gaussian derivative term
-- statement:
--   On the unit disk, each of the twenty mixed shift and covariance derivative integrals is bounded by the inverse Gaussian determinant times its individually specified sum of nonnegative Gaussian moments.
-- source:
--   Independent Price differentiation and rational interval certificate for Saha et al., arXiv:2608.11158v2. The density identity is Prove2Me bb4bfdfc-4dcc-425d-8a98-1b646de8d12b.

import Definitions.Def_GrothendieckLB_Supplement_cqPriceKernels

namespace GrothendieckLB.Supplement

theorem cq_price_partial_gaussian_bound (z : ℂ) (hz : ‖z‖<1)
    (t : CQPrice.Term) (ht : t∈CQPrice.terms) :
    ‖CQPrice.partialTerm z t.parameterOrder t.spatialOrder‖ ≤
      (2/Real.sqrt ‖1-z^2‖) * CQPrice.momentBound t (CQPrice.sigma z) := by sorry

end GrothendieckLB.Supplement

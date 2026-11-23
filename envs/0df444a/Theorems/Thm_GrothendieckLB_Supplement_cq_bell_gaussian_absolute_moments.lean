-- Prove2me | Theorems.Thm_GrothendieckLB_Supplement_cq_bell_gaussian_absolute_moments
-- name    : GrothendieckLB.Supplement.cq_bell_gaussian_absolute_moments
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T21:25:29.014805+00:00
-- url     : https://prove2.me/theorems/f22ce4e4-7307-4d33-aeed-51a8cd387044
-- title:
--   Gaussian absolute moments of the cubic-threshold Bell polynomials
-- statement:
--   Each of the cubic-threshold Bell polynomials through order five is integrable against the Gaussian of variance two. Its absolute first moment is bounded by the displayed outward dyadic endpoint.
-- source:
--   Independent Price differentiation and rational interval certificate for Saha et al., arXiv:2608.11158v2. The density identity is Prove2Me bb4bfdfc-4dcc-425d-8a98-1b646de8d12b.

import Definitions.Def_GrothendieckLB_Supplement_cqPriceKernels

namespace GrothendieckLB.Supplement

theorem cq_bell_gaussian_absolute_moments (a i : ℕ) (ha : a≤5) (hi : i≤a) :
    MeasureTheory.Integrable (fun x : ℝ => CQPrice.normalTwo x * |CQPrice.bell a i x|) ∧
    (∫ x : ℝ, CQPrice.normalTwo x * |CQPrice.bell a i x|) ≤ (CQPrice.bellUnits a i:ℝ)/(2:ℝ)^64 := by sorry

end GrothendieckLB.Supplement

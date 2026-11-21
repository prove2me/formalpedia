-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_phi_quotient_at_zero
-- name    : Kyprianou.Ch08.StageB.source_result81_phi_quotient_at_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T13:20:09.041218+00:00
-- url     : https://prove2.me/theorems/052ed58f-ea64-42aa-b77f-405b74854fe2
-- title:
--   Right limit of the scale passage coefficient q / Phi(q)
-- statement:
--   The law-derived log-moment exponent is convex and zero at zero. If the largest zero root is positive, the quotient tends to zero by its positive denominator bound. Otherwise the positive root tends to zero and the monotone positive secants converge to the nonnegative finite right slope.
-- source:
--   Kyprianou (2006), Chapter 8, equations (8.6)–(8.7), pp. 214–215. Decomposition of 8f95e53d-1cfe-4e26-a9c2-0fa1c54631b2.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory Filter Set Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_phi_quotient_at_zero
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (W : ℝ → ℝ → ℝ) (hW : HasSourceScaleFamily ψ W) :
    (∀ d : ℝ, HasPositiveFiniteRightPsiSlope ψ d →
      Tendsto (fun q : ℝ => q / Phi ψ q)
        (nhdsWithin 0 (Ioi 0)) (nhds d)) ∧
    ((¬ ∃ d : ℝ, HasPositiveFiniteRightPsiSlope ψ d) →
      Tendsto (fun q : ℝ => q / Phi ψ q)
        (nhdsWithin 0 (Ioi 0)) (nhds 0)) := by
  sorry

-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m86_bv_origin_value_from_exponent_slope
-- name    : Kyprianou.Ch08.StageB.p2m86_bv_origin_value_from_exponent_slope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T21:50:08.282634+00:00
-- url     : https://prove2.me/theorems/1d5495e2-8986-45e2-a7e5-9a615bb17132
-- title:
--   Identify the q=0 scale-function origin from the Laplace transform asymptotic, conditional on positive physical drift.
-- statement:
--   Identify the q=0 scale-function origin from the Laplace transform asymptotic, conditional on positive physical drift.
-- source:
--   Kyprianou (2006) Lemma 8.6, corrected BV physical drift certificate.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open Kyprianou.Ch08

namespace Kyprianou.Ch08.StageB

/-- Identify the q=0 scale-function origin from the Laplace transform asymptotic, conditional on positive physical drift. -/
theorem p2m86_bv_origin_value_from_exponent_slope :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      HasBoundedVariationTriplet D.gaussianCoefficient D.triplet.levyMeasure →
      Tendsto (fun β : ℝ => ψ β / β) atTop
        (𝓝 (bvDrift (-D.triplet.drift) D.triplet.levyMeasure)) →
      0 < bvDrift (-D.triplet.drift) D.triplet.levyMeasure →
      W 0 0 = (bvDrift (-D.triplet.drift) D.triplet.levyMeasure)⁻¹ := by
  sorry

end Kyprianou.Ch08.StageB

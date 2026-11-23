-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m86_bv_drift_positive_from_exponent_slope
-- name    : Kyprianou.Ch08.StageB.p2m86_bv_drift_positive_from_exponent_slope
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T21:49:59.419961+00:00
-- url     : https://prove2.me/theorems/3c36f7ef-d53f-42c1-872b-27ac50d8ae7d
-- title:
--   Positive physical bounded-variation drift from the exponent slope, using the spectrally negative model's exclusion of negative subordinators
-- statement:
--   Positive physical bounded-variation drift from the exponent slope, using the spectrally negative model's exclusion of negative subordinators.
-- source:
--   Kyprianou (2006) Lemma 8.6, corrected BV physical drift certificate.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open Kyprianou.Ch08

namespace Kyprianou.Ch08.StageB

/-- Positive physical bounded-variation drift from the exponent slope, using the spectrally negative model's exclusion of negative subordinators. -/
theorem p2m86_bv_drift_positive_from_exponent_slope :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      HasBoundedVariationTriplet D.gaussianCoefficient D.triplet.levyMeasure →
      Tendsto (fun β : ℝ => ψ β / β) atTop
        (𝓝 (bvDrift (-D.triplet.drift) D.triplet.levyMeasure)) →
      0 < bvDrift (-D.triplet.drift) D.triplet.levyMeasure := by
  sorry

end Kyprianou.Ch08.StageB

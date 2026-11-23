-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_6_zero_discount_v3
-- name    : Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T17:24:59.888139+00:00
-- url     : https://prove2.me/theorems/de926862-a36f-46c4-ab00-b71593f52cb1
-- title:
--   Corrected zero-discount origin dichotomy
-- statement:
--   Full source-faithful versioned Lemma 8.6 correction. Use bvDrift(-D.triplet.drift) to match the published characteristic exponent.
-- source:
--   Kyprianou (2006), Lemma 8.6, corrected using the published Kyprianou Chapter 1 positive characteristic exponent and Proved source_result81_law_positive_mgf.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory

namespace Kyprianou.Ch08.StageB

theorem source_result8_6_zero_discount_v3 :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ((W 0 0 = 0) ↔
        ¬ HasBoundedVariationTriplet D.gaussianCoefficient D.triplet.levyMeasure) ∧
      (HasBoundedVariationTriplet D.gaussianCoefficient D.triplet.levyMeasure →
        0 < bvDrift (-D.triplet.drift) D.triplet.levyMeasure ∧
        W 0 0 = (bvDrift (-D.triplet.drift) D.triplet.levyMeasure)⁻¹) := by
  sorry

end Kyprianou.Ch08.StageB

-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_6_bounded
-- name    : Kyprianou.Ch08.StageB.source_result8_6_bounded
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T23:57:38.105789+00:00
-- url     : https://prove2.me/theorems/017cd9b6-65a6-4319-b421-4515be57119d
-- title:
--   Chapter 8 Lemma 8.6 bounded-variation origin case
-- statement:
--   Bounded-variation half of Kyprianou Lemma 8.6: the drift d is positive and the q-scale value at zero is its reciprocal for all q≥0.
-- source:
--   Kyprianou (2006), Chapter 8 Lemma 8.6, printed p. 222.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB

theorem source_result8_6_bounded :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ q : ℝ, 0 ≤ q →
        (HasBoundedVariationTriplet
          D.gaussianCoefficient D.triplet.levyMeasure →
          0 < bvDrift D.triplet.drift D.triplet.levyMeasure ∧
          W q 0 =
            (bvDrift D.triplet.drift D.triplet.levyMeasure)⁻¹) := by
  sorry

end Kyprianou.Ch08.StageB

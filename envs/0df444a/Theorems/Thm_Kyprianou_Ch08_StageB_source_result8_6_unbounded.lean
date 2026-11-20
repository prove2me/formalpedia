-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_6_unbounded
-- name    : Kyprianou.Ch08.StageB.source_result8_6_unbounded
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T23:57:37.898254+00:00
-- url     : https://prove2.me/theorems/0a9ba1f1-d6c3-42aa-914d-f80e8d9bb628
-- title:
--   Chapter 8 Lemma 8.6 unbounded-variation origin case
-- statement:
--   Unbounded-variation half of Kyprianou Lemma 8.6: for every actual spectrally negative Levy model, q-scale value W^(q)(0) vanishes exactly in the unbounded-variation regime.
-- source:
--   Kyprianou (2006), Chapter 8 Lemma 8.6, printed p. 222.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB

theorem source_result8_6_unbounded :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ q : ℝ, 0 ≤ q →
        ((W q 0 = 0) ↔
          ¬ HasBoundedVariationTriplet
              D.gaussianCoefficient D.triplet.levyMeasure) := by
  sorry

end Kyprianou.Ch08.StageB

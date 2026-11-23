-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_6_zero_discount_v3_unbounded
-- name    : Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_unbounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T18:47:59.14992+00:00
-- url     : https://prove2.me/theorems/a0241ec9-2428-449a-960c-a4c43d89bc0d
-- title:
--   Corrected Lemma 8.6 zero-discount unbounded-variation branch
-- statement:
--   For a source-certified spectrally negative model with unbounded path variation, the zero-discount q-scale origin value vanishes. This isolates the large-frequency, superlinear Lévy exponent branch of corrected Lemma 8.6.
-- source:
--   Kyprianou (2006), Lemma 8.6. Exact branch of corrected source_result8_6_zero_discount_v3, UUID de926862-a36f-46c4-ab00-b71593f52cb1.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory

namespace Kyprianou.Ch08.StageB

theorem source_result8_6_zero_discount_v3_unbounded :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ¬ HasBoundedVariationTriplet D.gaussianCoefficient D.triplet.levyMeasure →
      W 0 0 = 0 := by
  sorry

end Kyprianou.Ch08.StageB

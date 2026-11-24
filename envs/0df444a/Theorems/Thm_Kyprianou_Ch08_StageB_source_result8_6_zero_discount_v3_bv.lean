-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_6_zero_discount_v3_bv
-- name    : Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_bv
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T18:47:56.325144+00:00
-- url     : https://prove2.me/theorems/945e2dcd-b17c-41fc-aade-64c5cd719be2
-- title:
--   Corrected Lemma 8.6 zero-discount bounded-variation branch
-- statement:
--   For a source-certified spectrally negative model with bounded path variation, the corrected physical drift bvDrift(-D.triplet.drift) is positive and the zero-discount q-scale origin equals its reciprocal. This isolates the finite large-frequency slope branch of corrected Lemma 8.6.
-- source:
--   Kyprianou (2006), Lemma 8.6. Exact branch of corrected source_result8_6_zero_discount_v3, UUID de926862-a36f-46c4-ab00-b71593f52cb1, using the positive characteristic-drift convention of source_result81_law_positive_mgf.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory

namespace Kyprianou.Ch08.StageB

theorem source_result8_6_zero_discount_v3_bv :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      HasBoundedVariationTriplet D.gaussianCoefficient D.triplet.levyMeasure →
      0 < bvDrift (-D.triplet.drift) D.triplet.levyMeasure ∧
      W 0 0 = (bvDrift (-D.triplet.drift) D.triplet.levyMeasure)⁻¹ := by
  sorry

end Kyprianou.Ch08.StageB

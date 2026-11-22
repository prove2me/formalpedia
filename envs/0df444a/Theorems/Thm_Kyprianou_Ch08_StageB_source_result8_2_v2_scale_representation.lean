-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_2_v2_scale_representation
-- name    : Kyprianou.Ch08.StageB.source_result8_2_v2_scale_representation
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T16:43:18.416943+00:00
-- url     : https://prove2.me/theorems/a2c584da-360d-4567-ae4c-ac67a244841f
-- title:
--   Theorem 8.2 source child: excursion-height scale representation
-- statement:
--   For the same spectrally negative model, Laplace exponent, source scale family, q and actual excursion-height measure as Theorem 8.2, prove the source scale representation: positivity of W_q at every positive height and the exact interval integral formula with the closed excursion tail n([t,∞)). This is the second conjunct of sourceCertificate_result8_2, separated without weakening its hypotheses or changing the atom convention.
-- source:
--   Source-faithful child extracted from the second conjunct of Kyprianou Chapter 8, Theorem 8.2, exact original 2006 edition SHA-256 3696f4b3373cabcd968e300994fdd70a04df97b57a16837ad672bac5a1c269bf; exact source definition sourceCertificate_result8_2 in Definitions.Def_Kyprianou_Ch08_StageCFoundation_D.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.source_result8_2_v2_scale_representation
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W)
    (q : ℝ) (hq : 0 ≤ q) (n : Measure ℝ)
    (hLaw : HasActualQExcursionHeightLaw P D ψ q n) :
    HasQExcursionScaleRepresentation ψ q (W q) n := by
  sorry

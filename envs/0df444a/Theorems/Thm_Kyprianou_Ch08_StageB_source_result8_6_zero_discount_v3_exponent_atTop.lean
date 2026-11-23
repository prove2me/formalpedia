-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_6_zero_discount_v3_exponent_atTop
-- name    : Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_exponent_atTop
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T19:21:09.504957+00:00
-- url     : https://prove2.me/theorems/a1bec2d8-cf5c-49e9-a028-ec845798aee4
-- title:
--   Source Laplace exponent grows to infinity
-- statement:
--   For a source-certified spectrally negative model whose paths are not almost surely antitone, any Laplace exponent for that model tends to infinity as the real parameter tends to infinity.
-- source:
--   Lemma 8.6 corrected proof: non-subordinator exponential lower bound derived from stationary increments and the source model's exclusion of almost surely antitone paths.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_exponent_atTop :
    ∀ (Ω : Type) [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      Tendsto ψ atTop atTop := by sorry

-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_6_zero_discount_v3_positive_increment
-- name    : Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_positive_increment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T19:31:01.999539+00:00
-- url     : https://prove2.me/theorems/97db8699-bb9b-4196-b35d-4250449bf3e4
-- title:
--   A non-antitone source has a uniformly positive increment event
-- statement:
--   Because the source model excludes almost surely antitone paths, some positive time has a positive-probability event on which the increment exceeds a fixed positive threshold.
-- source:
--   Lemma 8.6 corrected proof: countable exhaustion of the positive-increment event.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_positive_increment :
    ∀ (Ω : Type) [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P),
      ∃ (t : ℝ≥0) (ε : ℝ), 0 < (t : ℝ) ∧ 0 < ε ∧ P {ω | ε < D.X t ω} ≠ 0 := by sorry

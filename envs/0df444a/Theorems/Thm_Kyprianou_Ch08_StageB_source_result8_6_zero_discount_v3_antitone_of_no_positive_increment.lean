-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_6_zero_discount_v3_antitone_of_no_positive_increment
-- name    : Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_antitone_of_no_positive_increment
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T19:31:05.466799+00:00
-- url     : https://prove2.me/theorems/7ac49018-437c-4d68-8e5e-3b6d89b361ed
-- title:
--   No positive one-time increment forces antitone source paths
-- statement:
--   If every increment law puts zero mass on positive values, stationary increments and path right-continuity imply that every sample path is antitone.
-- source:
--   Lemma 8.6 corrected proof: stationary increments on a dense rational schedule plus right continuity.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_antitone_of_no_positive_increment :
    ∀ (Ω : Type) [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P),
      (∀ t : ℝ≥0, P {ω | 0 < D.X t ω} = 0) →
      ∀ (ω : Ω) (u v : ℝ≥0), u ≤ v → D.X v ω ≤ D.X u ω := by sorry

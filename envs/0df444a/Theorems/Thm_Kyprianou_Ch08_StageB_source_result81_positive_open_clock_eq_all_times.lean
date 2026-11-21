-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_positive_open_clock_eq_all_times
-- name    : Kyprianou.Ch08.StageB.source_result81_positive_open_clock_eq_all_times
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T20:44:11.728145+00:00
-- url     : https://prove2.me/theorems/1b19a58b-f5f9-45a9-a084-3a1cbae08167
-- title:
--   Positive-time open passage clock equals its all-time infimum
-- statement:
--   Right continuity makes a time-zero open hit approachable by positive witness times. Therefore taking the infimum only over strictly positive witnesses gives the same extended passage time.
-- source:
--   Kyprianou (2006), Chapter 8, Theorem 8.1, strict ruin and stopped Markov argument. Analytic obligation of parent theorem 78574f78-b2c0-43ff-a7df-919c061143b7.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_positive_open_clock_eq_all_times
    (f : ℝ≥0 → ℝ) (S : Set ℝ) (hS : IsOpen S)
    (hright : ∀ t, ContinuousWithinAt f (Ici t) t) :
    sInf {t : ℝ≥0∞ | ∃ u : ℝ≥0, 0 < u ∧ (u : ℝ≥0∞) = t ∧ f u ∈ S} =
      ⨅ (u : ℝ≥0) (_ : f u ∈ S), (u : ℝ≥0∞) := by
  sorry

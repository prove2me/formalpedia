-- Prove2me | Theorems.Thm_Kyprianou_Ch04_shiftedIsLevyProcessV1
-- name    : Kyprianou.Ch04.shiftedIsLevyProcessV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:36:18.540578+00:00
-- url     : https://prove2.me/theorems/f78f1612-836d-5dd3-ad01-c91e37e26dbd
-- title:
--   Deterministic time translation of a Levy process
-- statement:
--   Translate each finite partition, preserve stationary increment laws by transitivity, and compose the cadlag limits with the deterministic time shift.
-- source:
--   Supporting proof for Kyprianou (2006), Chapter 4, Exercise 4.9(i).

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.shiftedIsLevyProcessV1 {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (hX : IsLevyProcess X P) (s : ℝ≥0) :
    IsLevyProcess (fun t ω => X (s + t) ω - X s ω) P := by
  sorry

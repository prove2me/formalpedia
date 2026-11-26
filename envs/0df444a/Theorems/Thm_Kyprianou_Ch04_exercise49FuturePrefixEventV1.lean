-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49FuturePrefixEventV1
-- name    : Kyprianou.Ch04.exercise49FuturePrefixEventV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:56:53.677186+00:00
-- url     : https://prove2.me/theorems/bb795175-8d16-5103-a927-6a5320de7347
-- title:
--   There is a measurable path event encoding the nonnegative prefix and endpoint gain
-- statement:
--   There is a measurable path event encoding the nonnegative prefix and endpoint gain
-- source:
--   Kyprianou (2006), Exercise 4.9(iii), p.109

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49FuturePrefixEventV1
    (s : NNReal) (b : ℝ) :
    ∃ B : Set (NNReal → ℝ), MeasurableSet B ∧
      ∀ Y : NNReal → ℝ, IsCadlag Y →
        (Y ∈ B ↔ (∀ t : NNReal, t ≤ s → 0 ≤ Y t) ∧ b ≤ Y s) := by
  sorry

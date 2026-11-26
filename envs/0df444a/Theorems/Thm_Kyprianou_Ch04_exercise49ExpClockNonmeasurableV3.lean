-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49ExpClockNonmeasurableV3
-- name    : Kyprianou.Ch04.exercise49ExpClockNonmeasurableV3
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:48:58.208612+00:00
-- url     : https://prove2.me/theorems/d8ffd19f-2e63-561f-80a1-2b711a56e916
-- title:
--   A positive clock has a nonmeasurable sublevel in the countable-cocountable sigma algebra
-- statement:
--   A positive clock has a nonmeasurable sublevel in the countable-cocountable sigma algebra
-- source:
--   Kyprianou (2006), Exercise 4.9(iii), exceptional-path statement audit.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49ExpClockNonmeasurableV3
    [MeasurableSpace (ULift.{0} ℝ)]
    (hS : ∀ S : Set (ULift.{0} ℝ), MeasurableSet S ↔ S.Countable ∨ Sᶜ.Countable) :
    ∃ a : ULift.{0} ℝ → NNReal, (∀ e, 0 < a e) ∧
      ¬ MeasurableSet {e | a e ≤ 1} := by
  sorry

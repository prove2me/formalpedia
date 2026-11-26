-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49CountableCocountableSpaceV3
-- name    : Kyprianou.Ch04.exercise49CountableCocountableSpaceV3
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:48:55.69893+00:00
-- url     : https://prove2.me/theorems/ad671446-7c97-5592-91a3-2ff1b2474a35
-- title:
--   The countable or cocountable subsets form a sigma algebra
-- statement:
--   The countable or cocountable subsets form a sigma algebra
-- source:
--   Kyprianou (2006), Exercise 4.9(iii), exceptional-path statement audit.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49CountableCocountableSpaceV3
    {E : Type} :
    ∃ m : MeasurableSpace E, ∀ S : Set E,
      @MeasurableSet E m S ↔ S.Countable ∨ Sᶜ.Countable := by
  sorry

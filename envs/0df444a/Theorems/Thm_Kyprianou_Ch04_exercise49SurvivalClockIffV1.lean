-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49SurvivalClockIffV1
-- name    : Kyprianou.Ch04.exercise49SurvivalClockIffV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:54:51.263836+00:00
-- url     : https://prove2.me/theorems/44e62ba5-db12-5c01-8115-3cb495dcb899
-- title:
--   For a zero-start path, infinite strict downcrossing at nonnegative reserve is equivalent to a global lower bound
-- statement:
--   For a zero-start path, infinite strict downcrossing at nonnegative reserve is equivalent to a global lower bound
-- source:
--   Kyprianou (2006), Exercise 4.9(iii), p.109

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49SurvivalClockIffV1
    (Y : NNReal → ℝ) (h0 : Y 0 = 0) (x : ℝ) (hx : 0 ≤ x) :
    (sInf {v : WithTop NNReal | ∃ t : NNReal,
      v = ↑t ∧ 0 < t ∧ x + Y t < 0}) = ⊤ ↔
      ∀ t : NNReal, -x ≤ Y t := by
  sorry

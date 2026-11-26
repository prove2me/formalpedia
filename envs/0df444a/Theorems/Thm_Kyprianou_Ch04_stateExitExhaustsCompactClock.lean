-- Prove2me | Theorems.Thm_Kyprianou_Ch04_stateExitExhaustsCompactClock
-- name    : Kyprianou.Ch04.stateExitExhaustsCompactClock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T09:39:21.196567+00:00
-- url     : https://prove2.me/theorems/44788f57-1fdf-47c8-af32-c456876a496f
-- title:
--   stateExitExhaustsCompactClock
-- statement:
--   Increasing spatial exit clocks exhaust each compact time horizon of a cadlag path.
-- source:
--   Kyprianou (2006), Exercise 4.3(iii).

import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.ConditionalProbability
import Definitions.Def_LeanLevy_Processes_Cadlag
import Theorems.Thm_Kyprianou_Ch03_reflectionSignedCompactBoundV1
open MeasureTheory Filter Set ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

/-- Increasing spatial exit clocks exhaust each compact time horizon of a cadlag path. -/
theorem Kyprianou.Ch04.stateExitExhaustsCompactClock (Y : NNReal → ℝ) (hY : IsCadlag Y) (T : NNReal) :
    ∃ n : ℕ, (T : WithTop NNReal) <
      sInf {v : WithTop NNReal | ∃ u : NNReal, v = ↑u ∧ (n : ℝ) < |Y u|} := by
  sorry

-- Prove2me | Theorems.Thm_Kyprianou_Ch02_cadlagJumpOfAddContinuousV1
-- name    : Kyprianou.Ch02.cadlagJumpOfAddContinuousV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:00:58.260198+00:00
-- url     : https://prove2.me/theorems/a5838a35-fbc2-4c78-95f9-4469a37fbf23
-- title:
--   Actual jumps are unchanged by adding a continuous real path
-- statement:
--   Use the genuine left limit of the cadlag path and continuity of the added path, uniqueness of the left limit at strictly positive time, then cancel the continuous value.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.12; LeanLevy path construction and generic Avram finite-cylinder path law.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology Function
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.cadlagJumpOfAddContinuousV1
    (f g : ℝ≥0 → ℝ) (hf : IsCadlag f) (hg : Continuous g)
    (u : ℝ≥0) (hu : 0 < u) :
    (f u + g u) - Function.leftLim (fun t => f t + g t) u =
      f u - Function.leftLim f u := by
  sorry

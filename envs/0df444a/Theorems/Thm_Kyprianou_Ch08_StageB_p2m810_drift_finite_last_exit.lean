-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_drift_finite_last_exit
-- name    : Kyprianou.Ch08.StageB.p2m810_drift_finite_last_exit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T21:50:40.180169+00:00
-- url     : https://prove2.me/theorems/192a46a5-8854-43ed-853c-a61aea7b44f3
-- title:
--   An eventually nonnegative shifted path has finite last negative visit.
-- statement:
--   An eventually nonnegative shifted path has finite last negative visit.
-- source:
--   Kyprianou (2006), Exercise 8.10(iii)

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m810_drift_finite_last_exit
    (f : ℝ≥0 → ℝ) (y : ℝ) (h : Tendsto f atTop atTop) :
    lastExitShifted (fun t (_ : Unit) => f t) y () ≠ ⊤ := by
  sorry

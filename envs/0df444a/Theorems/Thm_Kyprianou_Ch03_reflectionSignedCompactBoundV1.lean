-- Prove2me | Theorems.Thm_Kyprianou_Ch03_reflectionSignedCompactBoundV1
-- name    : Kyprianou.Ch03.reflectionSignedCompactBoundV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T18:58:53.206102+00:00
-- url     : https://prove2.me/theorems/5ab2c3fe-bd00-431c-92a1-5d6ce9cb8949
-- title:
--   Signed càdlàg path bounded on compact intervals
-- statement:
--   Scalar multiplication preserves both one-sided limits, and càdlàg paths are bounded on compact intervals.
-- source:
--   Kyprianou (2006), Exercise 3.2, running maximum restart.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_LevyExtrema_SBA_runSup
import Definitions.Def_Kyprianou_Ch03_ReflectedProcesses
open MeasureTheory ProbabilityTheory Filter Kyprianou.Ch03
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch03.reflectionSignedCompactBoundV1
    (g : NNReal → ℝ) (hg : IsCadlag g) (c : ℝ) (t : NNReal) :
    BddAbove ((fun s => c * g s) '' Set.Icc 0 t) := by sorry

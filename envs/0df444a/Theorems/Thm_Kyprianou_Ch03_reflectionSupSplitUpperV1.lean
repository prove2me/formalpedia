-- Prove2me | Theorems.Thm_Kyprianou_Ch03_reflectionSupSplitUpperV1
-- name    : Kyprianou.Ch03.reflectionSupSplitUpperV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T18:59:02.282969+00:00
-- url     : https://prove2.me/theorems/dcc2cdfe-1a3d-4d3e-888b-f3509ffc7894
-- title:
--   Upper bound for translated running maximum
-- statement:
--   Partition points according to whether they precede a, or write them as a plus a nonnegative offset.
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

theorem Kyprianou.Ch03.reflectionSupSplitUpperV1
    (g : NNReal → ℝ) (a t : NNReal)
    (hb : BddAbove (g '' Set.Icc 0 (a+t)))
    : LevyExtrema.SBA.runSup g (a+t) ≤
      max (LevyExtrema.SBA.runSup g a) (LevyExtrema.SBA.runSup (fun s => g (a+s) - g a) t + g a) := by sorry

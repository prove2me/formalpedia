-- Prove2me | Theorems.Thm_Kyprianou_Ch03_reflectionSupSplitLowerV1
-- name    : Kyprianou.Ch03.reflectionSupSplitLowerV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T18:59:08.749128+00:00
-- url     : https://prove2.me/theorems/9774c540-431a-4d1f-a61c-a79d31109183
-- title:
--   Lower bound for translated running maximum
-- statement:
--   Both earlier and shifted intervals lie in the full interval.
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

theorem Kyprianou.Ch03.reflectionSupSplitLowerV1
    (g : NNReal → ℝ) (a t : NNReal)
    (hb : BddAbove (g '' Set.Icc 0 (a+t)))
    : max (LevyExtrema.SBA.runSup g a) (LevyExtrema.SBA.runSup (fun s => g (a+s) - g a) t + g a) ≤
      LevyExtrema.SBA.runSup g (a+t) := by sorry

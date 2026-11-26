-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41FiniteCorrectionSeriesV19
-- name    : Kyprianou.Ch04.exercise41FiniteCorrectionSeriesV19
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T13:20:05.041388+00:00
-- url     : https://prove2.me/theorems/9156f574-b6ac-5afd-b31c-efeb629bff1a
-- title:
--   Subtract a finitely supported correction from a finitely supported series
-- statement:
--   Subtract a finitely supported correction from a finitely supported series
-- source:
--   Kyprianou (2006), Exercise 4.1(ii).

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical Kyprianou.Ch04
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41FiniteCorrectionSeriesV19
    {ι : Type} (d z : ι → ℝ)
    (hd : Set.Finite (Function.support d))
    (hz : Set.Finite (Function.support z)) :
    Summable (fun s => ‖d s - z s‖) ∧
    (∑' s, (d s - z s)) = (∑' s, d s) - (∑' s, z s) := by
  sorry

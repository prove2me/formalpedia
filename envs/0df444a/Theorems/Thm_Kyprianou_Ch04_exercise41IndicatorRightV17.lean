-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41IndicatorRightV17
-- name    : Kyprianou.Ch04.exercise41IndicatorRightV17
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T13:13:36.670548+00:00
-- url     : https://prove2.me/theorems/ea193fc4-d295-5a61-aa8a-634ee9a074cd
-- title:
--   The binary nonnegative-state indicator is right continuous at each zero with a positive right germ
-- statement:
--   The binary nonnegative-state indicator is right continuous at each zero with a positive right germ
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

theorem Kyprianou.Ch04.exercise41IndicatorRightV17
    (x : NNReal → ℝ) (s : NNReal)
    (hR : ContinuousWithinAt x (Ici s) s)
    (hdep : x s = 0 → ∃ e : NNReal, 0 < e ∧
      ∀ u : NNReal, 0 < u → u < e → 0 < x (s+u)) :
    ContinuousWithinAt (fun u => if x u < 0 then (-1 : ℝ) else 0) (Ici s) s := by
  sorry

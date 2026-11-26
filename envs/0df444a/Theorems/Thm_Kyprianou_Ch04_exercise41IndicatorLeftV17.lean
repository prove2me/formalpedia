-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41IndicatorLeftV17
-- name    : Kyprianou.Ch04.exercise41IndicatorLeftV17
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T13:13:42.609721+00:00
-- url     : https://prove2.me/theorems/e06f769b-a840-44fc-9e70-51f6918983dc
-- title:
--   The left limit of the binary nonnegative-state indicator equals the strict-positive indicator of the physical left value minus one
-- statement:
--   The left limit of the binary nonnegative-state indicator equals the strict-positive indicator of the physical left value minus one
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

theorem Kyprianou.Ch04.exercise41IndicatorLeftV17
    (x : NNReal → ℝ) (s : NNReal) (hs : 0 < s) (l : ℝ)
    (hL : Tendsto x (nhdsWithin s (Iio s)) (nhds l))
    (harr : l = 0 → ∃ e : NNReal, 0 < e ∧
      ∀ u : NNReal, 0 < u → u < min e s → x (s-u) < 0) :
    Tendsto (fun u => if x u < 0 then (-1 : ℝ) else 0)
      (nhdsWithin s (Iio s)) (nhds (if 0 < l then 0 else -1)) := by
  sorry

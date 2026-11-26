-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41CadlagPhysicalJumpsCountableV17
-- name    : Kyprianou.Ch04.exercise41CadlagPhysicalJumpsCountableV17
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T13:13:55.062007+00:00
-- url     : https://prove2.me/theorems/a0de1c2e-0581-4a7b-be41-2d5ec717a5c6
-- title:
--   Physical jump support is countable for cadlag paths
-- statement:
--   Physical jump support is countable for cadlag paths
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

theorem Kyprianou.Ch04.exercise41CadlagPhysicalJumpsCountableV17
    (x l : NNReal → ℝ)
    (hR : ∀ s, ContinuousWithinAt x (Ici s) s)
    (hL : ∀ s, 0 < s → Tendsto x (nhdsWithin s (Iio s)) (nhds (l s))) :
    Set.Countable {s : NNReal | 0 < s ∧ x s ≠ l s} := by
  sorry

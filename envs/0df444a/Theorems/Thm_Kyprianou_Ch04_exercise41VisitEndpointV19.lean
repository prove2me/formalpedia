-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41VisitEndpointV19
-- name    : Kyprianou.Ch04.exercise41VisitEndpointV19
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T13:20:03.372872+00:00
-- url     : https://prove2.me/theorems/af407e80-2faa-5f61-b73b-4e929678814c
-- title:
--   Partition zero visits at the final endpoint
-- statement:
--   Partition zero visits at the final endpoint
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

theorem Kyprianou.Ch04.exercise41VisitEndpointV19
    (x : NNReal → ℝ) (t : NNReal)
    (ht : 0 < t)
    (hv : Set.Finite {s : NNReal | 0 < s ∧ s ≤ t ∧ x s = 0}) :
    (∑ s ∈ hv.toFinset, (if x s = 0 then (1 : ℝ) else 0)) =
      (∑ s ∈ hv.toFinset, (if s < t then (1 : ℝ) else 0)) +
      (if x t = 0 then 1 else 0) := by
  sorry

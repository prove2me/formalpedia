-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41VisitIndicatorTsumV19
-- name    : Kyprianou.Ch04.exercise41VisitIndicatorTsumV19
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T13:20:18.915331+00:00
-- url     : https://prove2.me/theorems/f9c053f9-2b49-41be-8d32-253477b47d96
-- title:
--   Finite support and sum for a subset of positive zero visits
-- statement:
--   Finite support and sum for a subset of positive zero visits
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

theorem Kyprianou.Ch04.exercise41VisitIndicatorTsumV19
    (x : NNReal → ℝ) (t : NNReal)
    (hv : Set.Finite {s : NNReal | 0 < s ∧ s ≤ t ∧ x s = 0})
    (p : NNReal → Prop) [DecidablePred p]
    (hp : ∀ s, 0 < s → p s → x s = 0) :
    Set.Finite (Function.support (fun s : Ioc (0 : NNReal) t => if p s then (1 : ℝ) else 0)) ∧
    (∑' s : Ioc (0 : NNReal) t, (if p s then (1 : ℝ) else 0)) =
      ∑ s ∈ hv.toFinset, (if p s then (1 : ℝ) else 0) := by
  sorry

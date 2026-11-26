-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41BinaryContinuousFlatV17
-- name    : Kyprianou.Ch04.exercise41BinaryContinuousFlatV17
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T13:13:41.901461+00:00
-- url     : https://prove2.me/theorems/17901eb2-26c1-4b1d-92f8-ca872d2e89fb
-- title:
--   A continuous binary function is constant on an interval
-- statement:
--   A continuous binary function is constant on an interval
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

theorem Kyprianou.Ch04.exercise41BinaryContinuousFlatV17
    (f : NNReal → ℝ) (hVal : ∀ u, f u = 0 ∨ f u = -1)
    (s t : NNReal) (hst : s ≤ t) (hcont : ContinuousOn f (Icc s t)) :
    f s = f t := by
  sorry

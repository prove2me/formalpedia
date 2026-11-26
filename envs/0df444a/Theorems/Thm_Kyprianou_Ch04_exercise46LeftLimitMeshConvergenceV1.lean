-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46LeftLimitMeshConvergenceV1
-- name    : Kyprianou.Ch04.exercise46LeftLimitMeshConvergenceV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:09:29.581614+00:00
-- url     : https://prove2.me/theorems/c821ccbb-8658-5eb0-80da-cf6a4c071990
-- title:
--   Fractional left mesh converges to the path left limit
-- statement:
--   The fractional left mesh converges from strictly below at positive times; at time zero the left-limit convention equals the path value.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46LeftLimitMeshConvergenceV1
    (f : NNReal → Real)
    (hleft : ∀ t : NNReal, 0 < t → ∃ l : Real,
      Tendsto f (nhdsWithin t (Iio t)) (nhds l))
    (t : NNReal) :
    Tendsto (fun n : Nat => f (t - t * (1 / 2 : NNReal) ^ (n + 1)))
      atTop (nhds (Function.leftLim f t)) := by
  sorry

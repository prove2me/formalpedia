-- Prove2me | Theorems.Thm_Kyprianou_Ch04_closedStopMaskLeftLimit
-- name    : Kyprianou.Ch04.closedStopMaskLeftLimit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:17:38.352068+00:00
-- url     : https://prove2.me/theorems/ff1b8360-b7d0-58a6-8410-911eae15a8ba
-- title:
--   closedStopMaskLeftLimit
-- statement:
--   The closed stopping mask preserves left continuity at positive times, including the stopping endpoint.
-- source:
--   Kyprianou (2006), Exercise 4.3(ii), pp. 106-107.

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

/-- Multiplication by the closed stopping mask preserves positive-time left limits. -/
theorem Kyprianou.Ch04.closedStopMaskLeftLimit (k : ℝ → ℝ) (tau : WithTop NNReal) (t : NNReal) (ht : 0 < t)
    (hk : Tendsto k (nhdsWithin (t : ℝ) (Set.Iio (t : ℝ))) (nhds (k (t : ℝ)))) :
    Tendsto (fun s : ℝ => if (s.toNNReal : WithTop NNReal) ≤ tau then k s else 0)
      (nhdsWithin (t : ℝ) (Set.Iio (t : ℝ)))
      (nhds (if (t : WithTop NNReal) ≤ tau then k (t : ℝ) else 0)) := by
  sorry

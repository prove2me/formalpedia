-- Prove2me | Theorems.Thm_Kyprianou_Ch04_strictMaskRightContinuous
-- name    : Kyprianou.Ch04.strictMaskRightContinuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T10:46:19.506316+00:00
-- url     : https://prove2.me/theorems/0fa0d81b-1257-4da9-977b-59cf71773ab4
-- title:
--   strictMaskRightContinuous
-- statement:
--   Strict clipping preserves right continuity on nonnegative time.
-- source:
--   Kyprianou (2006), Exercise 4.3(iii).

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

/-- Strict clipping preserves right continuity on nonnegative time. -/
theorem Kyprianou.Ch04.strictMaskRightContinuous (g : ℝ → ℝ) (tau : WithTop NNReal)
    (hr : ∀ r : ℝ, 0 ≤ r → ContinuousWithinAt g (Ici r) r) :
    ∀ r : ℝ, 0 ≤ r → ContinuousWithinAt
      (fun v => if (v.toNNReal : WithTop NNReal) < tau then g v else 0) (Ici r) r := by
  sorry

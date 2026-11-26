-- Prove2me | Theorems.Thm_Kyprianou_Ch04_leftLimitRealClockTendsto
-- name    : Kyprianou.Ch04.leftLimitRealClockTendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:45:25.634872+00:00
-- url     : https://prove2.me/theorems/4a801471-09aa-50c6-a083-731dd7fd7a2a
-- title:
--   leftLimitRealClockTendsto
-- statement:
--   The left-limit path is left-continuous at every positive real time.
-- source:
--   Kyprianou (2006), Exercise 4.3(ii), pp. 106-107.

import Mathlib
open Filter Set Topology
open scoped NNReal
set_option autoImplicit false

/-- Left limits of a nonnegative-time path yield a left-continuous left-limit path on real time. -/
theorem Kyprianou.Ch04.leftLimitRealClockTendsto (Y L : NNReal → ℝ)
    (hl : ∀ t : NNReal, 0 < t → Tendsto Y (nhdsWithin t (Iio t)) (nhds (L t))) :
    ∀ t : NNReal, 0 < t →
      Tendsto (fun s : ℝ => L s.toNNReal) (nhdsWithin (t : ℝ) (Iio (t : ℝ)))
        (nhds (L t)) := by
  sorry

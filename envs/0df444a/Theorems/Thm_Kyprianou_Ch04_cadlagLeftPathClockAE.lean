-- Prove2me | Theorems.Thm_Kyprianou_Ch04_cadlagLeftPathClockAE
-- name    : Kyprianou.Ch04.cadlagLeftPathClockAE
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:45:25.73621+00:00
-- url     : https://prove2.me/theorems/c1581daf-4e9b-5860-9231-9791d873a697
-- title:
--   cadlagLeftPathClockAE
-- statement:
--   A right-continuous real path agrees with its left-limit path at Lebesgue-almost every nonnegative time.
-- source:
--   Kyprianou (2006), Exercise 4.3(ii), pp. 106-107.

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

/-- The path and its left limit agree at Lebesgue-almost every nonnegative real time. -/
theorem Kyprianou.Ch04.cadlagLeftPathClockAE (Y L : NNReal → ℝ)
    (hr : ∀ t, ContinuousWithinAt Y (Ici t) t)
    (hl : ∀ t : NNReal, 0 < t → Tendsto Y (nhdsWithin t (Iio t)) (nhds (L t))) :
    ∀ᵐ s ∂volume.restrict (Ici (0 : ℝ)), Y s.toNNReal = L s.toNNReal := by
  sorry

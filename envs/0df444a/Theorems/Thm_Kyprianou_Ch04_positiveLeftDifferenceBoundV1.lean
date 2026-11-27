-- Prove2me | Theorems.Thm_Kyprianou_Ch04_positiveLeftDifferenceBoundV1
-- name    : Kyprianou.Ch04.positiveLeftDifferenceBoundV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T22:55:09.426304+00:00
-- url     : https://prove2.me/theorems/78cc8706-a15a-4444-9f5d-68535cf22103
-- title:
--   positiveLeftDifferenceBoundV1
-- statement:
--   positiveLeftDifferenceBoundV1
-- source:
--   Kyprianou (2006), Exercise 4.5(iii), physical clipped-grid uniform cutoff estimate

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.positiveLeftDifferenceBoundV1
    (Y Z L R : NNReal → ℝ) (T : NNReal) (d : ℝ)
    (hY : ∀ t, 0 < t → Tendsto Y (nhdsWithin t (Iio t)) (nhds (L t)))
    (hZ : ∀ t, 0 < t → Tendsto Z (nhdsWithin t (Iio t)) (nhds (R t)))
    (hb : ∀ t ≤ T, |Y t - Z t| ≤ d) :
    ∀ t ≤ T, 0 < t → |L t - R t| ≤ d := by
  sorry

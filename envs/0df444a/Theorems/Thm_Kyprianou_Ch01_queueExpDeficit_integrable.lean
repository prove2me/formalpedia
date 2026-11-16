-- Prove2me | Theorems.Thm_Kyprianou_Ch01_queueExpDeficit_integrable
-- name    : Kyprianou.Ch01.queueExpDeficit_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T11:26:32.135344+00:00
-- url     : https://prove2.me/theorems/a1af1932-241c-4504-98ab-4b0302b7edbb
-- title:
--   Integrability of the positive-support exponential deficit at nonnegative parameters
-- statement:
--   For a probability measure supported on strictly positive real numbers, its exponential deficit at a nonnegative parameter is between zero and one almost surely and therefore integrable.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.9(i), positive-claim exponential transform convexity

import Mathlib
open MeasureTheory Set
set_option autoImplicit false

theorem Kyprianou.Ch01.queueExpDeficit_integrable
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hpositive : F (Set.Iic (0 : ℝ)) = 0)
    (theta : ℝ) (ht : 0 ≤ theta) :
    Integrable (fun z : ℝ => 1 - Real.exp (-theta * z)) F := by sorry

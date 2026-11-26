-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_time_integral_error_bound
-- name    : Kyprianou.Ch04.ito43_time_integral_error_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:14:19.931737+00:00
-- url     : https://prove2.me/theorems/7f1a017c-ffc1-54c9-b51b-a549c07c62f4
-- title:
--   Variable subinterval integral error is bounded by full L1 error
-- statement:
--   Variable subinterval integral error is bounded by full L1 error.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3, supporting lemma.

import Mathlib
open MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

/-- An error integral over a variable subinterval is bounded by the full L1 error. -/

theorem Kyprianou.Ch04.ito43_time_integral_error_bound (a b : ℝ → ℝ) (T t : ℝ) (ht : t ≤ T)
    (ha : IntegrableOn a (Icc 0 T)) (hb : IntegrableOn b (Icc 0 T)) :
    |(∫ s in Icc 0 t, a s) - ∫ s in Icc 0 t, b s| ≤
      ∫ s in Icc 0 T, |a s - b s| := by sorry

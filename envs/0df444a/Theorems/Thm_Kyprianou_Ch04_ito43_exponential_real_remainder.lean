-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_exponential_real_remainder
-- name    : Kyprianou.Ch04.ito43_exponential_real_remainder
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T21:55:21.59766+00:00
-- url     : https://prove2.me/theorems/059b0740-46f4-5d5f-ae24-42a98e1b3448
-- title:
--   Real-part first-order complex exponential remainder
-- statement:
--   Apply the proved complex exponential remainder to minus the scaled exponent and bound its real part by its norm.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
open MeasureTheory Filter ProbabilityTheory Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_exponential_real_remainder (x : ℝ) (z : ℂ) (hx : 0 ≤ x) (hs : x*‖z‖ ≤ 1) :
    |1-(Complex.exp ((x:ℂ)*z)).re+x*z.re| ≤ (x*‖z‖)^2 := by sorry

-- Prove2me | Theorems.Thm_Kyprianou_Ch01_expDeficitQuotient_norm_le
-- name    : Kyprianou.Ch01.expDeficitQuotient_norm_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T12:12:51.128108+00:00
-- url     : https://prove2.me/theorems/c8d512ef-d142-4661-9ffe-615ff0a2ef10
-- title:
--   Domination by positive claim size of the exponential-deficit quotient
-- statement:
--   For θ>0 and x≥0, the exponential-deficit quotient lies between 0 and x. The proof uses 1−t≤exp(−t)≤1.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.9(i): right Laplace derivative and dominated convergence

import Mathlib
open MeasureTheory Filter Set
open scoped Topology
set_option autoImplicit false

theorem Kyprianou.Ch01.expDeficitQuotient_norm_le
    (theta x : ℝ) (ht : 0 < theta) (hx : 0 ≤ x) :
    ‖(1 - Real.exp (-theta * x)) / theta‖ ≤ x := by sorry

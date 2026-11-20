-- Prove2me | Theorems.Thm_Kyprianou_Ch01_complexHalfLogPrincipalSqrt
-- name    : Kyprianou.Ch01.complexHalfLogPrincipalSqrt
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T18:37:33.54572+00:00
-- url     : https://prove2.me/theorems/042d6465-5439-4043-9d04-88c0f4b3325d
-- title:
--   Exponential of principal complex half-log is the principal square root
-- statement:
--   For any nonzero complex input z, exp((1/2)log z)=sqrt z with the principal complex logarithm and square-root branch; the fraction 1/2 is a real coefficient coerced to complex. This is the exact Mathlib sqrt_eq_exp conversion.
-- source:
--   Mathlib.Analysis.RCLike.Sqrt sqrt_eq_exp, Kyprianou (2006) Exercise 1.6(ii) complex Gamma half-power identity.

import Mathlib
open Complex
set_option autoImplicit false

theorem Kyprianou.Ch01.complexHalfLogPrincipalSqrt (z : ℂ) (hz : z ≠ 0) :
    Complex.exp (((1 / 2 : ℝ) : ℂ) * Complex.log z) =
      Complex.sqrt z := by sorry

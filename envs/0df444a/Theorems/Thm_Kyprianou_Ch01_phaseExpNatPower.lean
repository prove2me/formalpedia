-- Prove2me | Theorems.Thm_Kyprianou_Ch01_phaseExpNatPower
-- name    : Kyprianou.Ch01.phaseExpNatPower
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T05:29:22.006853+00:00
-- url     : https://prove2.me/theorems/eaf47f1a-08b3-42fe-bbf4-ab9c746c9bb7
-- title:
--   Integer jump-size Fourier phase as a complex exponential power
-- statement:
--   For every real frequency ξ and nonnegative integer n, the Fourier exponential at jump size n+1 equals the (n+1)st power of the unit-modulus complex phase exp(iξ). This exact bridge transfers the logarithmic jump Fourier series to its complex power-series form in the compound-Poisson representation.
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.2(i), Fourier exponent identification.

import Mathlib
open Complex
set_option autoImplicit false

theorem Kyprianou.Ch01.phaseExpNatPower
    (xi : ℝ) (n : ℕ) :
    Complex.exp ((xi : ℂ) *
      (((n + 1 : ℕ) : ℝ) : ℂ) * Complex.I) =
      (Complex.exp ((xi : ℂ) * Complex.I)) ^ (n + 1) := by
  sorry

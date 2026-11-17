-- Prove2me | Theorems.Thm_Kyprianou_Ch01_logarithmicCompensatedExponent
-- name    : Kyprianou.Ch01.logarithmicCompensatedExponent
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T05:17:15.684201+00:00
-- url     : https://prove2.me/theorems/c8abbb7e-f91e-434d-892b-f12e325ece88
-- title:
--   Compensated logarithmic jump exponent in compound-Poisson form
-- statement:
--   For |q|<1 and |qz|<1, the sum of logarithmic jump intensities q^k/k times (z^k−1) equals log(1−q)−log(1−qz). This directly matches the characteristic exponent of the logarithmic-jump compound-Poisson representation in Kyprianou's Exercise 1.2(i).
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.2(i); logarithmic jump compound-Poisson representation.

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_logarithmicJumpComplexExponent
open Complex
set_option autoImplicit false

theorem Kyprianou.Ch01.logarithmicCompensatedExponent
    (q z : ℂ) (hq : ‖q‖ < 1) (hqz : ‖q * z‖ < 1) :
    (∑' n : ℕ,
      q ^ (n + 1) / ((n : ℂ) + 1) *
        (z ^ (n + 1) - 1)) =
      Complex.log (1 - q) - Complex.log (1 - q * z) := by
  sorry

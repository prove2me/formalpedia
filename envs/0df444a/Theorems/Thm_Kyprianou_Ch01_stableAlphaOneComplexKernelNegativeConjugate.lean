-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneComplexKernelNegativeConjugate
-- name    : Kyprianou.Ch01.stableAlphaOneComplexKernelNegativeConjugate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T12:30:13.234025+00:00
-- url     : https://prove2.me/theorems/e86a81ed-8d23-45d0-9779-ac5a15dea39b
-- title:
--   Conjugacy of the complex compensated alpha-one stable Levy kernel under frequency reversal
-- statement:
--   For any real z,r, the full compensated complex index-one stable Lévy kernel at frequency −z is the complex conjugate of the kernel at z. This preserves the source cutoff and supplies the negative-frequency symmetry required for the full alpha-one characteristic exponent from the positive-frequency logarithmic phase.
-- source:
--   Kyprianou (2006), Chapter 1, index-one stable characteristic exponent symmetry.

import Mathlib
open MeasureTheory Complex Set Real
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneComplexKernelNegativeConjugate
    (z r : ℝ) :
    ((1 : ℂ) - Complex.exp (Complex.I * ((((-z) * r : ℝ) : ℂ))) +
        Complex.I * ((((-z) * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ) =
      star (((1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
        Complex.I * (((z * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ)) := by
  sorry

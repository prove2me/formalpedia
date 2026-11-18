-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneComplexIntegralNegativeConjugate
-- name    : Kyprianou.Ch01.stableAlphaOneComplexIntegralNegativeConjugate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T12:33:05.064208+00:00
-- url     : https://prove2.me/theorems/5529b3bf-5160-4d32-a1f5-efa0e211556d
-- title:
--   Negative-frequency conjugacy of the fully compensated complex stable alpha-one Lévy integral
-- statement:
--   For every real frequency z, the positive-half-line Bochner integral of the source exact compensated alpha-one Lévy kernel at −z equals the complex conjugate of its integral at z. The proof integrates the Proved pointwise frequency-conjugacy identity and applies the pinned integral_conj theorem; it preserves the original cutoff r<1.
-- source:
--   Kyprianou (2006), Chapter 1, stable index-one characteristic exponent (1.8).

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneComplexKernelNegativeConjugate
open MeasureTheory Complex Set Real
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneComplexIntegralNegativeConjugate
    (z : ℝ) :
    (∫ r in Set.Ioi (0 : ℝ), ((1 : ℂ) - Complex.exp (Complex.I * ((((-z) * r : ℝ) : ℂ))) +
        Complex.I * ((((-z) * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ) ∂volume) =
      star (∫ r in Set.Ioi (0 : ℝ), ((1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
        Complex.I * (((z * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ) ∂volume) := by
  sorry

-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneLogPhaseImagKernel
-- name    : Kyprianou.Ch01.stableAlphaOneLogPhaseImagKernel
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T10:33:32.884196+00:00
-- url     : https://prove2.me/theorems/c5cfa33c-4e74-4e22-b614-530a9fc091ca
-- title:
--   Exact imaginary-part identity of the index-one compensated stable Lévy kernel
-- statement:
--   For any real z and r, the imaginary part of the fully compensated index-one Lévy integrand (1−exp(i z r)+i z r·1_(r<1))/r² equals (z r·1_(r<1)−sin(zr))/r². This preserves the original small-jump cutoff and isolates the logarithmic phase calculation from the previously proved cosine real part.
-- source:
--   Kyprianou (2006), Chapter 1, index-one stable logarithmic Lévy phase.

import Mathlib
open MeasureTheory Complex Set Real
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneLogPhaseImagKernel
    (z r : ℝ) :
    (((1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
        Complex.I * (((z * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ)).im =
      ((z * r) * (if r < 1 then 1 else 0) - Real.sin (z * r)) / r ^ 2 := by
  sorry

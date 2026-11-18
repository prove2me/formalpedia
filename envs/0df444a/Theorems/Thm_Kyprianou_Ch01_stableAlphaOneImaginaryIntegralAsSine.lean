-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneImaginaryIntegralAsSine
-- name    : Kyprianou.Ch01.stableAlphaOneImaginaryIntegralAsSine
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T12:13:37.108207+00:00
-- url     : https://prove2.me/theorems/3d6d2a5f-fc98-48d4-910f-2ed7fbf851d8
-- title:
--   Imaginary integral of the source stable alpha-one kernel equals the real sine phase integral
-- statement:
--   Whenever the original fully compensated complex alpha-one Lévy kernel is integrable, the imaginary part of its Bochner integral over r>0 equals the real sine integral (zr 1_(r<1)−sin(zr))/r². This is a rigorous integrable-projection step retaining the exact source cutoff.
-- source:
--   Kyprianou (2006), Chapter 1, stable index-one logarithmic Lévy phase.

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneLogPhaseImagKernel
open MeasureTheory Complex Set Real
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneImaginaryIntegralAsSine
    (z : ℝ)
    (hInt : IntegrableOn
      (fun r : ℝ => ((1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
        Complex.I * (((z * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ)) (Set.Ioi (0 : ℝ))) :
    (∫ r in Set.Ioi (0 : ℝ), ((1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
        Complex.I * (((z * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ) ∂volume).im =
      ∫ r in Set.Ioi (0 : ℝ),
        ((z * r) * (if r < 1 then (1 : ℝ) else 0) - Real.sin (z * r)) / r ^ 2 ∂volume := by
  sorry

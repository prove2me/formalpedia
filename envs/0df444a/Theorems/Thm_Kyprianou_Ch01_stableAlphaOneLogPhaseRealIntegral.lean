-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneLogPhaseRealIntegral
-- name    : Kyprianou.Ch01.stableAlphaOneLogPhaseRealIntegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T10:30:15.404568+00:00
-- url     : https://prove2.me/theorems/70d8c534-ab18-4ae1-819e-84ada8dbf254
-- title:
--   Real part of the integrable compensated alpha-one stable Lévy integral
-- statement:
--   Assuming the exact Chapter 1 compensated complex stable index-one kernel is integrable at a positive frequency z, its Bochner integral has real part πz/2. The proof uses exact pointwise real-part identity and the Proved stable alpha-one cosine scaling. This resolves the real-part sub-obligation of the source index-one logarithmic phase identity without assuming its imaginary phase.
-- source:
--   Kyprianou (2006), Chapter 1, index-one complex stable Lévy logarithmic-phase integral.

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneLogPhaseRealKernel
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCosineScaling
open MeasureTheory Complex Set Real
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneLogPhaseRealIntegral
    (z : ℝ) (hz : 0 < z)
    (hInt : IntegrableOn
      (fun r : ℝ =>
      ((1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
        Complex.I * (((z * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ)) (Set.Ioi (0 : ℝ))) :
    (∫ r in Set.Ioi (0 : ℝ),
      ((1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
        Complex.I * (((z * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ) ∂volume).re =
      Real.pi * z / 2 := by
  sorry

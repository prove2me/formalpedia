-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneLogPhaseImaginaryScaling
-- name    : Kyprianou.Ch01.stableAlphaOneLogPhaseImaginaryScaling
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T10:53:25.210066+00:00
-- url     : https://prove2.me/theorems/caeba901-1358-4888-926d-e1fdfb2526db
-- title:
--   Exact logarithmic frequency scaling of the imaginary alpha-one stable Lévy integral
-- statement:
--   For each positive frequency z, the imaginary compensated alpha-one stable kernel integral is z times its unit-frequency integral plus z log z. This is the source-consistent logarithmic cutoff correction derived by u=z r and integrating the difference of the cutoff functions over the interval from 1 to z. It makes the universal drift constant k equal to minus the unit-frequency imaginary integral.
-- source:
--   Kyprianou (2006), Chapter 1, index-one logarithmic phase.

import Mathlib
open MeasureTheory Set Real Complex
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneLogPhaseImaginaryScaling :
    ∀ z : ℝ, 0 < z →
    (∫ r in Set.Ioi (0 : ℝ), ((1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
        Complex.I * (((z * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ) ∂volume).im =
      z * ((∫ r in Set.Ioi (0 : ℝ), ((1 : ℂ) - Complex.exp (Complex.I * ((((1 : ℝ) * r : ℝ) : ℂ))) +
        Complex.I * ((((1 : ℝ) * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ) ∂volume).im + Real.log z) := by
  sorry

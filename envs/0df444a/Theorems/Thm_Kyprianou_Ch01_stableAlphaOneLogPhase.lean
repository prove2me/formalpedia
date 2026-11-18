-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneLogPhase
-- name    : Kyprianou.Ch01.stableAlphaOneLogPhase
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:19:44.717206+00:00
-- url     : https://prove2.me/theorems/e3defa1f-51d8-41ab-9dae-9b3ea6200c62
-- title:
--   Exercise 1.4(ii): index-one stable logarithmic characteristic-exponent phase
-- statement:
--   Kyprianou (2006), Exercise 1.4(ii), p. 28: at stable index α=1, prove there exists a real constant k independent of z such that the compensated Lévy integral ∫₀∞(1−e^{izr}+izr1_{r<1})r^(−2)dr = (π/2)z + iz log z − i k z, for every z>0. The integral's absolute integrability is included and the constant is a conclusion, not an assumed parameter. Together with the reflected integral this gives the full skew-stable characteristic exponent (1.8).
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.4(ii), printed p. 28, supporting formula (1.8).

import Mathlib
open MeasureTheory Set Real Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneLogPhase :
    ∃ k : ℝ, ∀ z : ℝ, 0 < z →
      IntegrableOn
        (fun r : ℝ =>
          ((1 : ℂ) -
              Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
            Complex.I * (((z * r : ℝ) : ℂ)) *
              (if r < 1 then (1 : ℂ) else 0)) /
            ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ))
        (Set.Ioi (0 : ℝ)) ∧
      (∫ r in Set.Ioi (0 : ℝ),
        ((1 : ℂ) -
            Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
          Complex.I * (((z * r : ℝ) : ℂ)) *
            (if r < 1 then (1 : ℂ) else 0)) /
          ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ)
          ∂volume) =
        (((Real.pi * z / 2 : ℝ) : ℂ)) +
          Complex.I * (((z * Real.log z : ℝ) : ℂ)) -
          Complex.I * (((k * z : ℝ) : ℂ)) := by
  sorry

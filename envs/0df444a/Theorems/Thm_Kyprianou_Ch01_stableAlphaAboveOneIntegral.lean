-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneIntegral
-- name    : Kyprianou.Ch01.stableAlphaAboveOneIntegral
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T08:19:59.102898+00:00
-- url     : https://prove2.me/theorems/28dfcdeb-77ad-4f9f-9507-f13124373206
-- title:
--   Exercise 1.4(iii): compensated complex stable exponent for 1<α<2
-- statement:
--   Kyprianou Exercise 1.4(iii): for 1<α<2, compute ∫₀∞(e^{ir}−1−ir)r^{−α−1}dr=Γ(−α)e^{−iπα/2}, including the compensated near-zero integrability. This analytic identity derives the stable exponent in equation (1.7), complementing the α<1 and α=1 cases. Draft awaiting remote elaboration.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.4(iii), printed p. 28.

import Mathlib
open MeasureTheory Filter Set Real
open scoped NNReal ENNReal Interval
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaAboveOneIntegral
    (alpha : ℝ) (ha1 : 1 < alpha) (ha2 : alpha < 2) :
    IntegrableOn
      (fun r : ℝ =>
        (Complex.exp (Complex.I * (r : ℂ)) - 1 -
          Complex.I * (r : ℂ)) / ((((r : ℝ) ^ (alpha + 1)) : ℝ) : ℂ))
      (Set.Ioi (0 : ℝ)) ∧
    (∫ r in Set.Ioi (0 : ℝ),
      (Complex.exp (Complex.I * (r : ℂ)) - 1 -
        Complex.I * (r : ℂ)) / ((((r : ℝ) ^ (alpha + 1)) : ℝ) : ℂ)
        ∂volume) =
      ((Real.Gamma (-alpha) : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * ((Real.pi * alpha / 2) : ℂ))) := by
  sorry

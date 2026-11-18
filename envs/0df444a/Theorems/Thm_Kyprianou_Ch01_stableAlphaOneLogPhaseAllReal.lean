-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneLogPhaseAllReal
-- name    : Kyprianou.Ch01.stableAlphaOneLogPhaseAllReal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T12:39:10.194885+00:00
-- url     : https://prove2.me/theorems/614636a7-3266-4288-8ca7-44c76d28259f
-- title:
--   Exceptional alpha-one stable Lévy logarithmic complex integral at every real frequency
-- statement:
--   There is a single real constant k such that for every real frequency xi, the exact positive-half-line compensated index-one Lévy kernel integral equals (pi/2)|xi| + i xi log|xi| − i k xi, with the convention log 0=0. It extends the Proved source logarithmic phase for positive frequencies to negative frequencies through Proved complex-integral conjugacy and covers zero explicitly. It is the source-integral ingredient of Kyprianou equation (1.8).
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.4(ii), stable index-one characteristic exponent (1.8).

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneLogPhase
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneComplexIntegralNegativeConjugate
open MeasureTheory Complex Set Real
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneLogPhaseAllReal :
    ∃ k : ℝ, ∀ xi : ℝ,
    (∫ r in Set.Ioi (0 : ℝ), ((1 : ℂ) - Complex.exp (Complex.I * (((xi * r : ℝ) : ℂ))) +
        Complex.I * (((xi * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ) ∂volume) =
      (((Real.pi * |xi| / 2 : ℝ) : ℂ) +
        Complex.I * (((xi * Real.log |xi| : ℝ) : ℂ)) -
        Complex.I * (((k * xi : ℝ) : ℂ))) := by
  sorry

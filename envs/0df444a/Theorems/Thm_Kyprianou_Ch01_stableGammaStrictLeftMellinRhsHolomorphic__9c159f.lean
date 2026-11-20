-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableGammaStrictLeftMellinRhsHolomorphic__9c159f
-- name    : Kyprianou.Ch01.stableGammaStrictLeftMellinRhsHolomorphic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T13:06:20.884586+00:00
-- url     : https://prove2.me/theorems/9c159fe9-7e1c-4489-9906-ac84e01c8f6f
-- title:
--   Holomorphy of the principal-branch Gamma Mellin expression in the strict left half-plane
-- statement:
--   The Gamma constant times exp((alpha-1)*log(-w)) is holomorphic at all complex w of strictly negative real part, because -w lies in the slit plane and the principal logarithm and exponential are analytic there. No extra positivity constraint on alpha is necessary.
-- source:
--   Kyprianou Chapter 1, Gamma-Mellin complex analytic continuation.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory Complex Real Set Filter Kyprianou.Ch01
set_option autoImplicit false

theorem Kyprianou.Ch01.stableGammaStrictLeftMellinRhsHolomorphic
    (alpha : ℝ) :
    AnalyticOnNhd ℂ
      (fun w : ℂ =>
        ((Real.Gamma (1 - alpha) : ℝ) : ℂ) *
          Complex.exp (((alpha - 1 : ℝ) : ℂ) * Complex.log (-w)))
      {w : ℂ | w.re < 0} := by sorry

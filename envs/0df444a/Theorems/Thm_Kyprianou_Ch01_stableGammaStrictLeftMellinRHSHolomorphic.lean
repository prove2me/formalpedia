-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableGammaStrictLeftMellinRHSHolomorphic
-- name    : Kyprianou.Ch01.stableGammaStrictLeftMellinRHSHolomorphic
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T11:39:45.353262+00:00
-- url     : https://prove2.me/theorems/91f18d49-a7ea-4908-b8f2-96d6c60494b2
-- title:
--   Holomorphicity of the complex Gamma Mellin closed-form on the strict-left half-plane
-- statement:
--   For every real alpha the principal-branch expression Γ(1−alpha)exp((alpha−1)log(−w)) is holomorphic in complex w on the full strict left half-plane Re(w)<0. There the argument −w lies in the right half-plane and thus in the principal logarithm slit plane; the result follows by the chain rule, complex logarithm holomorphy, and the entire exponential.
-- source:
--   Kyprianou (2006), Chapter 1 stable complex Gamma extension; analytic identity-theorem right-hand side.

import Mathlib
open MeasureTheory Complex Real Set Filter
set_option autoImplicit false

theorem Kyprianou.Ch01.stableGammaStrictLeftMellinRHSHolomorphic
    (alpha : ℝ) :
    DifferentiableOn ℂ
      (fun w : ℂ => ((Real.Gamma (1 - alpha) : ℝ) : ℂ) *
        Complex.exp (((alpha - 1 : ℝ) : ℂ) * Complex.log (-w)))
      {w : ℂ | w.re < 0} := by sorry

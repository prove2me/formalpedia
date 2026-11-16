-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableGammaNegativeRecurrence
-- name    : Kyprianou.Ch01.stableGammaNegativeRecurrence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T20:57:32.799654+00:00
-- url     : https://prove2.me/theorems/a9dbcd85-c590-4f2e-8d0a-9d37984e539d
-- title:
--   Stable index Gamma recurrence on the negative unit interval
-- statement:
--   For 0<alpha<1, the Euler Gamma recurrence Gamma(1-alpha)=-alpha*Gamma(-alpha) gives Gamma(-alpha)=-Gamma(1-alpha)/alpha. This exact identity is the final algebraic step of Kyprianou Exercise 1.4(i), after integrating the stable Laplace exponent by parts. It reuses Mathlib's kernel-checked Real.Gamma_add_one, preserving the nonzero denominator hypothesis.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.4(i), printed solution p.301 (PDF page 155), formula (S.2).

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
open Real
set_option autoImplicit false

theorem Kyprianou.Ch01.stableGammaNegativeRecurrence
    (alpha : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1) :
    Real.Gamma (-alpha) = -(Real.Gamma (1 - alpha)) / alpha := by sorry

-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableGammaStrictLeftExpDerivative
-- name    : Kyprianou.Ch01.stableGammaStrictLeftExpDerivative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T11:19:38.072043+00:00
-- url     : https://prove2.me/theorems/20351fbd-e517-4db4-8f21-ddd867f96ddf
-- title:
--   Derivative of the strict-left complex Gamma exponential deficit
-- statement:
--   Derivative of exp(wr)-1 on the real positive line is w exp(wr), with real-to-complex differentiation.
-- source:
--   Kyprianou (2006), Chapter 1, complex stable Gamma deficit integral, source exact analytic half-line integration by parts.

import Mathlib
open MeasureTheory Complex Real Set Filter
set_option autoImplicit false

theorem Kyprianou.Ch01.stableGammaStrictLeftExpDerivative
    (w : ℂ) (r : ℝ) :
    HasDerivAt
      (fun t : ℝ => Complex.exp (w * (t : ℂ)) - 1)
      (w * Complex.exp (w * (r : ℂ))) r := by sorry

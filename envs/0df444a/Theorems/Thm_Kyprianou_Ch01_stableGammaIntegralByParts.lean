-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableGammaIntegralByParts
-- name    : Kyprianou.Ch01.stableGammaIntegralByParts
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T20:59:10.599915+00:00
-- url     : https://prove2.me/theorems/586cf7ba-d135-4b8e-a060-90b2ffd56220
-- title:
--   Stable exponent exponential deficit integral via rigorous integration by parts
-- statement:
--   The actual analytic content of stable Gamma integral for 0<alpha<1: integrability at 0 and infinity, vanishing boundary contributions in integration by parts, and the exact relation ∫(e^-ux-1)x^-alpha-1 = -(u/alpha)∫e^-ux*x^-alpha. Integrate first on [epsilon,R], then pass epsilon↓0 and R↑∞ using dominated convergence from positive index. This source-faithful sublemma isolates all improper-integral analysis and leaves the gamma-recursion and Laplace-kernel scaling as separately proved public facts.
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.4(i), solution p.301 / PDF p.155, formula S.2.

import Mathlib
open MeasureTheory Set Real
set_option autoImplicit false

theorem Kyprianou.Ch01.stableGammaIntegralByParts
    (alpha u : ℝ) (ha0 : 0 < alpha) (ha1 : alpha < 1) (hu : 0 < u) :
    IntegrableOn (fun x : ℝ =>
      (Real.exp (-(u * x)) - 1) * x ^ (-alpha - 1))
      (Set.Ioi (0 : ℝ)) ∧
    (∫ x in Set.Ioi (0 : ℝ),
      (Real.exp (-(u * x)) - 1) * x ^ (-alpha - 1) ∂volume) =
    -(u / alpha) * (∫ x in Set.Ioi (0 : ℝ),
      Real.exp (-(u * x)) * x ^ (-alpha) ∂volume) := by sorry

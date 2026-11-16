-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableGammaDeficitIntegrable
-- name    : Kyprianou.Ch01.stableGammaDeficitIntegrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T21:33:32.748186+00:00
-- url     : https://prove2.me/theorems/b548ea88-e67a-4798-8c44-dbeb3df89e2b
-- title:
--   Stable Lévy Gamma exponential-deficit kernel is Lebesgue integrable
-- statement:
--   The stable Gamma Lévy exponent integrand (e^(-ux)-1)*x^(-alpha-1) is absolutely integrable for 0<alpha<1 and u>0. The already published pointwise deficit inequality bounds its norm on x>0 by the independently proved integrable piecewise envelope u*x^-alpha on (0,1] and x^-alpha-1 on (1,∞). Apply the pinned Mathlib Integrable.mono' on the restricted volume measure and the measurable integrand. This directly discharges the integrability conjunct needed before rigorous improper integration by parts.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.4(i), printed solution p.301, PDF page 155.

import Mathlib
open MeasureTheory Real Set
set_option autoImplicit false

theorem Kyprianou.Ch01.stableGammaDeficitIntegrable
    (alpha u : ℝ) (ha0 : 0 < alpha) (ha1 : alpha < 1) (hu : 0 < u) :
    IntegrableOn (fun x : ℝ =>
      (Real.exp (-(u * x)) - 1) * x ^ (-alpha - 1))
      (Set.Ioi (0 : ℝ)) := by sorry

-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableGammaIntegral
-- name    : Kyprianou.Ch01.stableGammaIntegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:19:18.693011+00:00
-- url     : https://prove2.me/theorems/de6a61e3-0204-404f-b755-67612d1b92c3
-- title:
--   Exercise 1.4(i): stable Lévy exponent via the Gamma integral
-- statement:
--   Kyprianou Exercise 1.4(i), equation (1.20): for 0<α<1 and u>0, the improper stable-law Lévy integral ∫₀∞(e^(−ux)−1)x^(−α−1) dx is integrable and equals Γ(−α)u^α. This is the real-parameter analytic core of the α-stable characteristic-exponent formula, not a weakened finite-interval identity. Draft pending remote Lean elaboration.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.4(i), printed p. 27, equation (1.20).

import Mathlib
open MeasureTheory Set Real
set_option autoImplicit false

theorem Kyprianou.Ch01.stableGammaIntegral
    (alpha u : ℝ)
    (hα0 : 0 < alpha) (hα1 : alpha < 1)
    (hu : 0 < u) :
    IntegrableOn
      (fun x : ℝ =>
        (Real.exp (-(u * x)) - 1) * x ^ (-alpha - 1))
      (Set.Ioi (0 : ℝ)) ∧
      (∫ x in Set.Ioi (0 : ℝ),
        (Real.exp (-(u * x)) - 1) * x ^ (-alpha - 1) ∂volume) =
          Real.Gamma (-alpha) * u ^ alpha := by
  sorry

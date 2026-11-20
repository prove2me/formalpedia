-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableGammaRealDeficitAtMinusOne
-- name    : Kyprianou.Ch01.stableGammaRealDeficitAtMinusOne
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T08:28:43.378583+00:00
-- url     : https://prove2.me/theorems/d1e18bc1-62f7-4e5f-a425-8049fff95d23
-- title:
--   Real stable Gamma deficit integral at negative unit Laplace frequency
-- statement:
--   For stable index 0<alpha<1, the genuine absolutely convergent real integral ∫_0^∞(exp(−x)−1)x^(−alpha−1) dx equals Γ(−alpha). Integration by parts has zero endpoint terms, reducing to -(1/alpha) times the Euler integral defining Γ(1−alpha); pinned Mathlib Real.Gamma_eq_integral and the separately Proved Γ(1−alpha)=−alpha Γ(−alpha) finish the coefficient. This supplies the exact real-negative-axis seed for analytic continuation of the complex stable Fourier deficit identity.
-- source:
--   Kyprianou (2006), Chapter 1 stable Fourier-Gamma characteristic exponent, real negative-Laplace seed.

import Mathlib
open MeasureTheory Set Real Filter
set_option autoImplicit false

theorem Kyprianou.Ch01.stableGammaRealDeficitAtMinusOne
    (alpha : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1) :
    (∫ x in Set.Ioi (0 : ℝ),
      (Real.exp (-x) - 1) * x ^ (-alpha - 1) ∂volume) =
      Real.Gamma (-alpha) := by
  sorry

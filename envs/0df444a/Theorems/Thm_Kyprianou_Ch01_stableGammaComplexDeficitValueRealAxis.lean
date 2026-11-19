-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableGammaComplexDeficitValueRealAxis
-- name    : Kyprianou.Ch01.stableGammaComplexDeficitValueRealAxis
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T22:58:52.085038+00:00
-- url     : https://prove2.me/theorems/7b2599f6-3718-407b-99c7-1c3e5d22afa3
-- title:
--   Stable Gamma complex deficit integral on the negative real axis
-- statement:
--   The exact complex integral of the stable deficit kernel at negative real w=-u is the real gamma constant times the principal complex power of positive u. This is the analytic identity on the negative real axis under α∈(0,1), following by coercion from the proved real stable Gamma integral.
-- source:
--   Kyprianou 2006, Ch1 stable gamma complex Fourier-Laplace integral; exact split of stableGammaComplexDeficitValue.

import Mathlib
open MeasureTheory Set Complex Real Filter
set_option autoImplicit false

theorem Kyprianou.Ch01.stableGammaComplexDeficitValueRealAxis
    (alpha u : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1)
    (hu : 0 < u) :
    (∫ r in Set.Ioi (0 : ℝ),
      (Complex.exp (-(u : ℂ) * (r : ℂ)) - 1) *
        ((r ^ (-alpha - 1) : ℝ) : ℂ) ∂volume) =
      ((Real.Gamma (-alpha) : ℝ) : ℂ) *
        Complex.exp ((alpha : ℂ) * Complex.log (u : ℂ)) := by
  sorry

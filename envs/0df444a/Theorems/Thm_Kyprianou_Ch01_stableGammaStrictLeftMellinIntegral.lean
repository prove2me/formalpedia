-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableGammaStrictLeftMellinIntegral
-- name    : Kyprianou.Ch01.stableGammaStrictLeftMellinIntegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T11:12:52.479186+00:00
-- url     : https://prove2.me/theorems/57199057-ae24-4feb-82d5-14e6f0755073
-- title:
--   Complex Mellin Gamma formula in the strict right Laplace half-plane
-- statement:
--   This is the source-exact complex Laplace/Mellin integral, valid for Re(w)<0. It is the analytic core of the Γ(−alpha) stable Lévy exponent identity.
-- source:
--   Kyprianou (2006) Chapter 1 stable index 0<alpha<1, complex Lévy exponent Gamma transform.

import Mathlib
open MeasureTheory Complex Real Set Filter
set_option autoImplicit false

theorem Kyprianou.Ch01.stableGammaStrictLeftMellinIntegral
    (alpha : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1)
    (w : ℂ) (hwre : w.re < 0) :
    (∫ r in Set.Ioi (0 : ℝ),
      Complex.exp (w * (r : ℂ)) *
        ((r ^ (-alpha) : ℝ) : ℂ) ∂volume) =
      ((Real.Gamma (1 - alpha) : ℝ) : ℂ) *
        Complex.exp (((alpha - 1 : ℝ) : ℂ) * Complex.log (-w)) := by sorry

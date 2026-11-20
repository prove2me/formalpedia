-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableGammaComplexDeficitValueStrictLeft
-- name    : Kyprianou.Ch01.stableGammaComplexDeficitValueStrictLeft
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T23:12:24.309184+00:00
-- url     : https://prove2.me/theorems/16d4bd13-c01e-4ba4-ad7e-f8db907af77a
-- title:
--   Stable Gamma complex integral in the strict left half-plane
-- statement:
--   Exact complex Gamma stable-deficit formula for Re w<0, without restrictions on Im w. Intended proof by holomorphic extension from negative real w using the established real-axis formula and identity theorem.
-- source:
--   Kyprianou 2006 Chapter 1 stable Gamma identity in closed left half plane; exact subcases of nonreal analytic extension.

import Mathlib
open MeasureTheory Set Complex Real Filter
set_option autoImplicit false

theorem Kyprianou.Ch01.stableGammaComplexDeficitValueStrictLeft
    (alpha : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1)
    (w : ℂ) (hw : w ≠ 0) (hwre : w.re < 0) :
    (∫ r in Set.Ioi (0 : ℝ),
      (Complex.exp (w * (r : ℂ)) - 1) *
        ((r ^ (-alpha - 1) : ℝ) : ℂ) ∂volume) =
      ((Real.Gamma (-alpha) : ℝ) : ℂ) *
        Complex.exp ((alpha : ℂ) * Complex.log (-w)) := by
  sorry

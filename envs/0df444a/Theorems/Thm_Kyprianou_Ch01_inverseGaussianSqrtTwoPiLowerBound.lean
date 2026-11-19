-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianSqrtTwoPiLowerBound
-- name    : Kyprianou.Ch01.inverseGaussianSqrtTwoPiLowerBound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T00:59:18.724727+00:00
-- url     : https://prove2.me/theorems/031b7bba-0606-411b-bda2-1e290d73e5ab
-- title:
--   Inverse Gaussian normalising square-root constant exceeds one
-- statement:
--   The real normalising factor sqrt(2π) appearing in the original inverse-Gaussian Lévy density is at least one. This is an elementary exact inequality needed for the real truncated moment piecewise upper envelope, with no external assumptions.
-- source:
--   Kyprianou (2006), Chapter 1 inverse-Gaussian density normalisation, exact pointwise power envelope.

import Mathlib
open Real
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianSqrtTwoPiLowerBound : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi) := by
  sorry

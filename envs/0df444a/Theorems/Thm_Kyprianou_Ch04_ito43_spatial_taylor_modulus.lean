-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_spatial_taylor_modulus
-- name    : Kyprianou.Ch04.ito43_spatial_taylor_modulus
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:43:35.05085+00:00
-- url     : https://prove2.me/theorems/7424a11f-2ff3-5d90-a73e-fe7c51ca7e45
-- title:
--   Second-order Taylor error controlled by second derivative oscillation
-- statement:
--   Second-order Taylor error controlled by second derivative oscillation.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3, supporting lemma.

import Mathlib
open Set
set_option autoImplicit false

/-- Second-order Taylor error controlled by the oscillation of the second derivative. -/

theorem Kyprianou.Ch04.ito43_spatial_taylor_modulus (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (x y c M : ℝ)
    (hM : 0 ≤ M) (hb : ∀ z ∈ uIcc x y, |iteratedDeriv 2 f z - c| ≤ M) :
    |f y - f x - deriv f x * (y-x) - c * (y-x)^2 / 2| ≤ M * (y-x)^2 / 2 := by sorry

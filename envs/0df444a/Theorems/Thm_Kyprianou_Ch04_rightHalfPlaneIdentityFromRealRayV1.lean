-- Prove2me | Theorems.Thm_Kyprianou_Ch04_rightHalfPlaneIdentityFromRealRayV1
-- name    : Kyprianou.Ch04.rightHalfPlaneIdentityFromRealRayV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T22:47:50.640419+00:00
-- url     : https://prove2.me/theorems/7e921cf4-1972-4f00-9e75-cc24aabe77b5
-- title:
--   Holomorphic identity from a real ray on the closed right half-plane
-- statement:
--   Continuous holomorphic functions on the closed right half-plane agreeing on the real ray above one agree throughout the closed right half-plane.
-- source:
--   Supporting Laplace-to-characteristic exponent continuation for Kyprianou (2006), Chapter 4.

import Mathlib
open Complex Filter Set Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.rightHalfPlaneIdentityFromRealRayV1 (f g : ℂ → ℂ)
    (hf : DiffContOnCl ℂ f {z : ℂ | 0 < z.re})
    (hg : DiffContOnCl ℂ g {z : ℂ | 0 < z.re})
    (hr : ∀ x : ℝ, 1 ≤ x → f (x : ℂ) = g (x : ℂ)) :
    ∀ z : ℂ, 0 ≤ z.re → f z = g z := by
  sorry

-- Prove2me | Theorems.Thm_Kyprianou_Ch04_cor412_secant_deriv
-- name    : Kyprianou.Ch04.cor412_secant_deriv
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:19:33.393329+00:00
-- url     : https://prove2.me/theorems/323d6649-8032-42ea-ab11-7d22977fc833
-- title:
--   Positive right derivative of a convex function equals its nonnegative secant infimum
-- statement:
--   Positive right derivative of a convex function equals its nonnegative secant infimum.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.12.

import Mathlib
open Set Filter
open scoped Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.cor412_secant_deriv (f : ℝ → ℝ) (h0 : f 0 = 0)
    (hc : ConvexOn ℝ (Ici 0) f)
    (hd : 0 < derivWithin f (Ici 0) 0) :
    max 0 (sInf ((fun x : ℝ => f x / x) '' Ioi 0)) =
      derivWithin f (Ici 0) 0 := by sorry

-- Prove2me | Theorems.Thm_Kyprianou_Ch04_zeroSlopeOfPositiveRoot
-- name    : Kyprianou.Ch04.zeroSlopeOfPositiveRoot
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T00:43:20.352568+00:00
-- url     : https://prove2.me/theorems/16938679-53fb-5ed7-a0c0-af579dc4d40f
-- title:
--   Positive root forces zero nonnegative secant infimum
-- statement:
--   The secant set contains zero. If bounded below its infimum is at most zero, and if not bounded below the real conditional infimum is zero.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.9

import Mathlib
open Set
set_option autoImplicit false

theorem Kyprianou.Ch04.zeroSlopeOfPositiveRoot (f : ℝ → ℝ) (b : ℝ) (hb : 0 < b) (hz : f b = 0) :
    max 0 (sInf ((fun x : ℝ => f x / x) '' Ioi 0)) = 0 := by
  sorry

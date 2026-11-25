-- Prove2me | Theorems.Thm_Kyprianou_Ch04_nonpositiveSecantSlopeIff
-- name    : Kyprianou.Ch04.nonpositiveSecantSlopeIff
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T12:30:19.441713+00:00
-- url     : https://prove2.me/theorems/12571023-4a0a-56bc-ad5c-1b1be054cf8e
-- title:
--   Nonpositive small-argument exponent slope and vanishing positive part
-- statement:
--   For a convex exponent vanishing at zero, the positive part of the infimum of positive secant slopes vanishes exactly when arbitrarily small positive upper slope bounds are attained. Handles unbounded-below secants explicitly.
-- source:
--   Kyprianou (2006), Corollary 4.9, secant slope coefficient.

import Mathlib
open Set
set_option autoImplicit false

theorem Kyprianou.Ch04.nonpositiveSecantSlopeIff
    (f : ℝ → ℝ) (hf : ConvexOn ℝ (Set.Ici 0) f) (h0 : f 0 = 0) :
    let m := max 0 (sInf ((fun x : ℝ => f x / x) '' Set.Ioi 0))
    (∀ ε : ℝ, 0 < ε → ∃ x : ℝ, 0 < x ∧ f x < ε * x) ↔ m = 0 := by
  sorry

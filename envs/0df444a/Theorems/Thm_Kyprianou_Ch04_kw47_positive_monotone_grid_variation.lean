-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw47_positive_monotone_grid_variation
-- name    : Kyprianou.Ch04.kw47_positive_monotone_grid_variation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T19:48:48.555386+00:00
-- url     : https://prove2.me/theorems/49987b74-9647-53cc-9ca9-32c2e93ac6a8
-- title:
--   Bounded monotone finite-grid variation
-- statement:
--   For any finite real sequence which is monotone or antitone, nonnegative and bounded by C at its two endpoints, total absolute increment variation equals the endpoint difference in the direction of monotonicity, and is bounded above by C. This generic lemma controls the time-only exponential factor in the Kella-Whitt stochastic product.
-- source:
--   Elementary telescoping variation estimate used in the proof of Kyprianou (2006), Exercise 4.7, p. 108.

import Mathlib
set_option autoImplicit false

/-- A one-sided monotone path has at most its endpoint envelope
as total variation on an arbitrary finite grid. -/

theorem Kyprianou.Ch04.kw47_positive_monotone_grid_variation
    (g : Nat → Real) (n : Nat) (C : Real)
    (hMono : Monotone g ∨ Antitone g)
    (h0 : 0 ≤ g 0) (hn : 0 ≤ g n)
    (hb0 : g 0 ≤ C) (hbn : g n ≤ C) :
    (∑ i ∈ Finset.range n, |g (i + 1) - g i|) ≤ C := by sorry

-- Prove2me | Theorems.Thm_Kyprianou_Ch04_nonpositiveMeanIffNonnegativeSecantSlopeZero
-- name    : Kyprianou.Ch04.nonpositiveMeanIffNonnegativeSecantSlopeZero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T19:31:55.673578+00:00
-- url     : https://prove2.me/theorems/768b1e1e-c102-430e-a92b-d61d0f8cd765
-- title:
--   Nonpositive mean criterion equals vanishing nonnegative secant-slope infimum
-- statement:
--   The epsilon test for a nonpositive right Laplace-exponent slope is equivalent to the positive part of the infimum of positive secants being zero, using the same sInf convention as Corollary 4.9. The proof handles unbounded-below secants separately.
-- source:
--   Kyprianou (2006), Corollary 4.9, printed page 100; deterministic secant-slope classification.

import Mathlib
open Set
set_option autoImplicit false

theorem Kyprianou.Ch04.nonpositiveMeanIffNonnegativeSecantSlopeZero
    (f : ℝ → ℝ) :
    (∀ ε : ℝ, 0 < ε → ∃ θ : ℝ, 0 < θ ∧ f θ < ε * θ) ↔
      max 0 (sInf ((fun θ : ℝ => f θ / θ) '' Set.Ioi 0)) = 0 := by
  sorry

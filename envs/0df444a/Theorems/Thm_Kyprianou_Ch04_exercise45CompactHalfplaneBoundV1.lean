-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45CompactHalfplaneBoundV1
-- name    : Kyprianou.Ch04.exercise45CompactHalfplaneBoundV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:29:40.910561+00:00
-- url     : https://prove2.me/theorems/39aee29a-1e85-5166-bc08-f913b40eb5f0
-- title:
--   Compact rectangle support and continuity give a bound on the positive half-plane
-- statement:
--   A jointly continuous real function on the nonnegative-time half-plane that vanishes outside a compact rectangle admits a positive uniform bound.
-- source:
--   Kyprianou (2006), Exercise 4.5(iv), localisation argument.

import Mathlib
open Set
set_option autoImplicit false

/-- A continuous function supported on a compact rectangle is bounded on the positive half-plane. -/
theorem Kyprianou.Ch04.exercise45CompactHalfplaneBoundV1 (g : ℝ → ℝ → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hc : ContinuousOn (fun z : ℝ × ℝ => g z.1 z.2) (Ici (0 : ℝ) ×ˢ univ))
    (hz : ∀ s x, 0 ≤ s → (R < s ∨ R < |x|) → g s x = 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ s x, 0 ≤ s → |g s x| ≤ K := by
  sorry

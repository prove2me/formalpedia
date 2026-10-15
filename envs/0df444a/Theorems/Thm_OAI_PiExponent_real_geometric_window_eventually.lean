-- Prove2me | Theorems.Thm_OAI_PiExponent_real_geometric_window_eventually
-- name    : OAI.PiExponent.real_geometric_window_eventually
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-14T09:36:55.731532+00:00
-- url     : https://prove2.me/theorems/8d18804a-7259-4232-bb95-c187cb30d121
-- title:
--   An eventual bound for a geometric window before rounding
-- statement:
--   If $0<\theta<1$, $b>0$, and $b^2\theta<1$, then from some natural exponent onward the rounded-up real endpoint $b^m/8+1$ satisfies the strict upper bound. The child captures the decay of the three terms in the expansion.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PiExponent.lean

import Mathlib.Data.Real.Basic

theorem OAI.PiExponent.real_geometric_window_eventually
    (theta b : ℝ) (htheta : 0 < theta) (htheta_one : theta < 1)
    (hb : 0 < b) (hgap : b ^ 2 * theta < 1) :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
      (b ^ m / 8 + 1) ^ 2 * theta ^ m < 1 := by sorry

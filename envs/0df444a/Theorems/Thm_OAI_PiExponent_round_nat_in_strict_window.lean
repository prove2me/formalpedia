-- Prove2me | Theorems.Thm_OAI_PiExponent_round_nat_in_strict_window
-- name    : OAI.PiExponent.round_nat_in_strict_window
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-14T09:37:04.750314+00:00
-- url     : https://prove2.me/theorems/861db3aa-3a1b-4a56-bb3c-4ca565b9e6c3
-- title:
--   Round a positive real endpoint upward to a natural number
-- statement:
--   For positive real $x$ and $q$, if $(x+1)^2q<1$, an integer strictly above $x$ can be chosen no larger than $x+1$, so it remains below the strict upper bound. When $x$ is an integer, the next integer handles the equality boundary.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PiExponent.lean

import Mathlib.Data.Real.Basic

theorem OAI.PiExponent.round_nat_in_strict_window
    (x q : ℝ) (hx : 0 < x) (hq : 0 < q)
    (hbound : (x + 1) ^ 2 * q < 1) :
    ∃ K : ℕ, 0 < K ∧ (K : ℝ) ^ 2 * q < 1 ∧ x < (K : ℝ) := by sorry

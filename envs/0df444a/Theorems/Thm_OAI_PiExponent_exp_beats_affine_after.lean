-- Prove2me | Theorems.Thm_OAI_PiExponent_exp_beats_affine_after
-- name    : OAI.PiExponent.exp_beats_affine_after
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-14T09:06:01.802784+00:00
-- url     : https://prove2.me/theorems/d9d9692b-2693-4ebc-b416-3275a1987d1e
-- title:
--   An exponential eventually exceeds every affine function
-- statement:
--   For every real base greater than one, real affine coefficients, and natural cutoff, some positive exponent beyond the cutoff makes the displayed exponential quotient exceed the affine expression.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PiExponent.lean

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Order

theorem OAI.PiExponent.exp_beats_affine_after
    (R p q : ℝ) (hR : 1 < R) (M : ℕ) :
    ∃ m : ℕ, M ≤ m ∧ 0 < m ∧
      p * (m : ℝ) + q < R ^ m / (8 * ((m : ℝ) + 1)) := by sorry

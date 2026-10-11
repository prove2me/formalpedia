-- Prove2me | Theorems.Thm_OAI_PiExponent_pi_floor_bracket_lower_bound
-- name    : OAI.PiExponent.pi_floor_bracket_lower_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-10T22:33:42.105306+00:00
-- url     : https://prove2.me/theorems/a65c6978-0919-4c12-97db-2beaaec550ec
-- title:
--   Uniform lower bounds at the integer endpoints bracketing q pi
-- statement:
--   For every real exponent nu greater than 2, there is a natural threshold Q at least 2 such that for every natural q at least Q, both rational numbers floor(q*pi)/q and (floor(q*pi)+1)/q have distance from pi at least q^(-nu).
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PiExponent.lean

import Mathlib

theorem OAI.PiExponent.pi_floor_bracket_lower_bound (nu : ℝ) (hnu : 2 < nu) :
    ∃ Q : ℕ, 2 ≤ Q ∧
      ∀ q : ℕ, Q ≤ q →
        (q : ℝ) ^ (-nu) ≤
          |Real.pi - ((Int.floor ((q : ℝ) * Real.pi) : ℤ) : ℝ) / (q : ℝ)| ∧
        (q : ℝ) ^ (-nu) ≤
          |Real.pi - (((Int.floor ((q : ℝ) * Real.pi) + 1 : ℤ) : ℝ) / (q : ℝ))| := by
  sorry

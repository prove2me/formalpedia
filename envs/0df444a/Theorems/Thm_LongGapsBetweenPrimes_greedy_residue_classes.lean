-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_greedy_residue_classes
-- name    : LongGapsBetweenPrimes.greedy_residue_classes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:37:46.74851+00:00
-- url     : https://prove2.me/theorems/f2c6eaef-68f8-40d5-9c26-8cb69413552d
-- title:
--   Long Gaps Between Primes: greedy residue classes
-- statement:
--   The greedy product bound in (2.1), before applying Mertens' estimate.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L409-L462
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L409-L462

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.greedy_residue_classes (S ps : Finset ℕ) (hpos : ∀ p ∈ ps, 0 < p) :
    ∃ a : ℕ → ℕ, (∀ p ∈ ps, a p < p) ∧
      ((survivors S ps a).card : ℝ) ≤ (S.card : ℝ) * ∏ p ∈ ps, (1 - 1 / (p : ℝ)) := by sorry

-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_assignmentVariance_tuple
-- name    : LongGapsBetweenPrimes.assignmentVariance_tuple
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:42:11.571802+00:00
-- url     : https://prove2.me/theorems/c8649bb8-0376-471b-963b-77e0f4be0eab
-- title:
--   Long Gaps Between Primes: assignment Variance tuple
-- statement:
--   A tuple's assignment variance is the product of its reciprocal totients.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2208-L2218
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2208-L2218

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.assignmentVariance_tuple {P k : ℕ} (hP : Squarefree P) (r : DivisorTuple P k)
    (hpair : ∀ i j, i ≠ j → Nat.Coprime (r i).val (r j).val) :
    assignmentVariance (fun p : PrimeIndex P => p.val) (tupleAssignment r) =
      ∏ i, 1 / ((r i).val.totient : ℝ) := by sorry

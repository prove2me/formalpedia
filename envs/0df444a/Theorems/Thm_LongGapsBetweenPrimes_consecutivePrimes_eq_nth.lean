-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_consecutivePrimes_eq_nth
-- name    : LongGapsBetweenPrimes.consecutivePrimes_eq_nth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:48:57.115429+00:00
-- url     : https://prove2.me/theorems/0cf39f76-ae77-428c-8cb5-70c713952d80
-- title:
--   Long Gaps Between Primes: consecutive Primes eq nth
-- statement:
--   Consecutive primes occur at adjacent indices in the prime enumeration.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L4486-L4499
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L4486-L4499

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.consecutivePrimes_eq_nth {p q : ℕ} (h : ConsecutivePrimes p q) :
    ∃ n : ℕ, Nat.nth Nat.Prime n = p ∧ Nat.nth Nat.Prime (n + 1) = q := by sorry

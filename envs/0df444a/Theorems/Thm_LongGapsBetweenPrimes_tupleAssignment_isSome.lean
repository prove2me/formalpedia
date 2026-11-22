-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_tupleAssignment_isSome
-- name    : LongGapsBetweenPrimes.tupleAssignment_isSome
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:42:04.543954+00:00
-- url     : https://prove2.me/theorems/b914a677-2bf8-494c-b3ad-42e299270fb0
-- title:
--   Long Gaps Between Primes: tuple Assignment is Some
-- statement:
--   A prime is assigned precisely when it divides the tuple product.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2139-L2143
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2139-L2143

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.tupleAssignment_isSome {P k : ℕ} (r : DivisorTuple P k) (p : PrimeIndex P) :
    (tupleAssignment r p).isSome ↔ p.val ∣ tupleProduct r := by sorry

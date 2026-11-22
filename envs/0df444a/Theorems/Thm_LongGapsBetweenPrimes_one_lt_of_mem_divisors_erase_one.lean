-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_one_lt_of_mem_divisors_erase_one
-- name    : LongGapsBetweenPrimes.one_lt_of_mem_divisors_erase_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:29:45.508615+00:00
-- url     : https://prove2.me/theorems/ff8cc45d-52c6-4f8f-8585-2f08ea9de61e
-- title:
--   Long Gaps Between Primes: one lt of mem divisors erase one
-- statement:
--   A divisor other than one is greater than one.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L58-L61
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L58-L61

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.one_lt_of_mem_divisors_erase_one {P d : ℕ}
    (hd : d ∈ P.divisors.erase 1) : 1 < d := by sorry

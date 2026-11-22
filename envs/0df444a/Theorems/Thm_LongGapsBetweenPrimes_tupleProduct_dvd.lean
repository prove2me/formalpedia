-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_tupleProduct_dvd
-- name    : LongGapsBetweenPrimes.tupleProduct_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:34:44.481813+00:00
-- url     : https://prove2.me/theorems/c06f5426-423b-41a7-849a-ce0cf6b5d048
-- title:
--   Long Gaps Between Primes: tuple Product dvd
-- statement:
--   The product of pairwise coprime divisors of `P` divides `P`.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2132-L2136
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2132-L2136

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.tupleProduct_dvd {P k : ℕ} (r : DivisorTuple P k)
    (hpair : ∀ i j, i ≠ j → Nat.Coprime (r i).val (r j).val) : tupleProduct r ∣ P := by sorry

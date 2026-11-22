-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_prime_coordinate_unique
-- name    : LongGapsBetweenPrimes.prime_coordinate_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:41:55.392728+00:00
-- url     : https://prove2.me/theorems/876163a5-e1a8-4d90-bff7-c69300f812cc
-- title:
--   Long Gaps Between Primes: prime coordinate unique
-- statement:
--   A prime divides at most one coordinate of a pairwise coprime tuple.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2066-L2070
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2066-L2070

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.prime_coordinate_unique {P k p : ℕ} (hp : p.Prime) (r : DivisorTuple P k)
    (hpair : ∀ i j, i ≠ j → Nat.Coprime (r i).val (r j).val)
    {i j : Fin k} (hi : p ∣ (r i).val) (hj : p ∣ (r j).val) : i = j := by sorry

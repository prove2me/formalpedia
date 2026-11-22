-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_auxiliaryPrimes_prime
-- name    : LongGapsBetweenPrimes.auxiliaryPrimes_prime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:29:43.452811+00:00
-- url     : https://prove2.me/theorems/73e7f121-103a-4c71-be16-e3961a4867e4
-- title:
--   Long Gaps Between Primes: auxiliary Primes prime
-- statement:
--   Every auxiliary prime is prime.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1189-L1190
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1189-L1190

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.auxiliaryPrimes_prime {Z Y p : ℕ} (hp : p ∈ auxiliaryPrimes Z Y) : p.Prime := by sorry

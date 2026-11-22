-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_prod_primeIndex_dvd
-- name    : LongGapsBetweenPrimes.prod_primeIndex_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:32:12.589915+00:00
-- url     : https://prove2.me/theorems/9aaefa87-402d-41f6-9140-f62f3054113f
-- title:
--   Long Gaps Between Primes: prod prime Index dvd
-- statement:
--   Restrict a product over primes dividing `P` to those dividing `d`.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2123-L2129
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2123-L2129

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.prod_primeIndex_dvd {P d : ℕ} (hP : P ≠ 0) (hd : d ∣ P)
    {M : Type*} [CommMonoid M] (f : ℕ → M) :
    (∏ p : PrimeIndex P, if p.val ∣ d then f p.val else 1) = ∏ p ∈ d.primeFactors, f p := by sorry

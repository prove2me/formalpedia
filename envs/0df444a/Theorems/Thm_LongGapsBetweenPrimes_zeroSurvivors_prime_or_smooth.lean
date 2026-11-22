-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_zeroSurvivors_prime_or_smooth
-- name    : LongGapsBetweenPrimes.zeroSurvivors_prime_or_smooth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:47:59.86688+00:00
-- url     : https://prove2.me/theorems/b19f4aa5-05bf-4a3c-a9b7-5403ebbae304
-- title:
--   Long Gaps Between Primes: zero Survivors prime or smooth
-- statement:
--   A zero-sieve survivor is prime or has all prime factors at most the smoothness cutoff.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L4119-L4133
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L4119-L4133

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.zeroSurvivors_prime_or_smooth {x : ℝ} {H n : ℕ} (hx : 0 < x)
    (hsmall : 2 * (H : ℝ) < x * (coverW x : ℝ)) (hn : n ∈ zeroSurvivors x H) :
    n.Prime ∨ ∀ p : ℕ, p.Prime → p ∣ n → p ≤ coverZ x := by sorry

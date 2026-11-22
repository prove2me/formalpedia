-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_prime_dvd_assignmentProduct
-- name    : LongGapsBetweenPrimes.prime_dvd_assignmentProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:44:07.40007+00:00
-- url     : https://prove2.me/theorems/bc69711c-0d38-4a87-b928-b5e78fecba26
-- title:
--   Long Gaps Between Primes: prime dvd assignment Product
-- statement:
--   Every assigned prime divides the assignment product.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2628-L2631
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2628-L2631

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.prime_dvd_assignmentProduct {P k : ℕ} (σ : PrimeIndex P → Option (Fin k))
    (p : PrimeIndex P) (hp : (σ p).isSome) :
    p.val ∣ assignmentProduct (fun p : PrimeIndex P => p.val) σ := by sorry

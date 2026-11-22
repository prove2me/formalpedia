-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_assignmentPrimes_product
-- name    : LongGapsBetweenPrimes.assignmentPrimes_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:35:09.861107+00:00
-- url     : https://prove2.me/theorems/934cb9f4-b802-4fa3-b608-8bb2698cb029
-- title:
--   Long Gaps Between Primes: assignment Primes product
-- statement:
--   The product of the assigned primes equals the assignment product.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2400-L2403
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2400-L2403

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.assignmentPrimes_product {P k : ℕ} (σ : PrimeIndex P → Option (Fin k)) :
    (∏ p ∈ assignmentPrimes σ, p) = assignmentProduct (fun p : PrimeIndex P => p.val) σ := by sorry

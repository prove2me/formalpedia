-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_assignmentPrimes_subset
-- name    : LongGapsBetweenPrimes.assignmentPrimes_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:35:03.390441+00:00
-- url     : https://prove2.me/theorems/46f344d1-9946-430d-b498-e9b736d5b81e
-- title:
--   Long Gaps Between Primes: assignment Primes subset
-- statement:
--   Every assigned prime divides `P`.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2382-L2386
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2382-L2386

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.assignmentPrimes_subset {P k : ℕ} (σ : PrimeIndex P → Option (Fin k)) :
    assignmentPrimes σ ⊆ P.primeFactors := by sorry

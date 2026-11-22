-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_assignmentProduct_primeFactors
-- name    : LongGapsBetweenPrimes.assignmentProduct_primeFactors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:43:12.335169+00:00
-- url     : https://prove2.me/theorems/a19c6867-2001-465d-a5ab-579e1b9cc562
-- title:
--   Long Gaps Between Primes: assignment Product prime Factors
-- statement:
--   The prime factors of the assignment product are exactly the assigned primes.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2418-L2421
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2418-L2421

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.assignmentProduct_primeFactors {P k : ℕ} (σ : PrimeIndex P → Option (Fin k)) :
    (assignmentProduct (fun p : PrimeIndex P => p.val) σ).primeFactors = assignmentPrimes σ := by sorry

-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_assignmentProduct_dvd
-- name    : LongGapsBetweenPrimes.assignmentProduct_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:43:06.8016+00:00
-- url     : https://prove2.me/theorems/62416ae5-7dc9-4591-acec-cc22af48d8dd
-- title:
--   Long Gaps Between Primes: assignment Product dvd
-- statement:
--   The product of the assigned primes divides `P`.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2411-L2415
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2411-L2415

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.assignmentProduct_dvd {P k : ℕ} (σ : PrimeIndex P → Option (Fin k)) :
    assignmentProduct (fun p : PrimeIndex P => p.val) σ ∣ P := by sorry

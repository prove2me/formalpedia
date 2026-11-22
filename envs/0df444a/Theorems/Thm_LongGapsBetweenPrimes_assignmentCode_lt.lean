-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_assignmentCode_lt
-- name    : LongGapsBetweenPrimes.assignmentCode_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:43:18.519865+00:00
-- url     : https://prove2.me/theorems/3a363739-03e3-40eb-9a2c-d7e79bbeec9f
-- title:
--   Long Gaps Between Primes: assignment Code lt
-- statement:
--   The assignment code is smaller than its modulus.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2454-L2457
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2454-L2457

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.assignmentCode_lt {P k : ℕ} (root : (p : PrimeIndex P) → Fin k → Fin p.val)
    (σ : PrimeIndex P → Option (Fin k)) :
    assignmentCode root σ < assignmentProduct (fun p : PrimeIndex P => p.val) σ := by sorry

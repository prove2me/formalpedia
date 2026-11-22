-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_assignmentProduct_pos
-- name    : LongGapsBetweenPrimes.assignmentProduct_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:43:07.167888+00:00
-- url     : https://prove2.me/theorems/be023e40-426c-4f21-8c6a-e41e9decbb05
-- title:
--   Long Gaps Between Primes: assignment Product pos
-- statement:
--   The product of the assigned primes is positive.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2406-L2408
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2406-L2408

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.assignmentProduct_pos {P k : ℕ} (σ : PrimeIndex P → Option (Fin k)) :
    0 < assignmentProduct (fun p : PrimeIndex P => p.val) σ := by sorry

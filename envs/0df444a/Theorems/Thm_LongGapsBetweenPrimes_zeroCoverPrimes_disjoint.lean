-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_zeroCoverPrimes_disjoint
-- name    : LongGapsBetweenPrimes.zeroCoverPrimes_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:48:27.341151+00:00
-- url     : https://prove2.me/theorems/73f861a7-8044-47db-95d5-7332140bf41e
-- title:
--   Long Gaps Between Primes: zero Cover Primes disjoint
-- statement:
--   The zero-residue and greedy prime sets are disjoint.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L4279-L4283
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L4279-L4283

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.zeroCoverPrimes_disjoint (x : ℝ) :
    Disjoint (zeroCoverPrimes x) (auxiliaryPrimes (coverW x) (coverZ x)) := by sorry

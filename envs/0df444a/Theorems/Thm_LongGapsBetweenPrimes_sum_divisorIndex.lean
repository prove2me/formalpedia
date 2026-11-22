-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_sum_divisorIndex
-- name    : LongGapsBetweenPrimes.sum_divisorIndex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:29:46.587394+00:00
-- url     : https://prove2.me/theorems/42346bc7-9c0a-4bb5-b848-c1cdd2c2e1d8
-- title:
--   Long Gaps Between Primes: sum divisor Index
-- statement:
--   Rewrite a sum over divisor indices as a sum over the divisor finset.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L284-L286
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L284-L286

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.sum_divisorIndex (P : ℕ) (f : ℕ → ℝ) :
    (∑ d : DivisorIndex P, f d.val) = ∑ d ∈ P.divisors, f d := by sorry

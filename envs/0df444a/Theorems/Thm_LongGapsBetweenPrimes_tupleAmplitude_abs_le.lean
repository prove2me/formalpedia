-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_tupleAmplitude_abs_le
-- name    : LongGapsBetweenPrimes.tupleAmplitude_abs_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:44:03.131806+00:00
-- url     : https://prove2.me/theorems/1f103322-7bbf-45ef-9966-30adb0ed65ac
-- title:
--   Long Gaps Between Primes: tuple Amplitude abs le
-- statement:
--   Coefficients bounded by one give tuple amplitudes bounded by one.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2620-L2625
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2620-L2625

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.tupleAmplitude_abs_le {P k : ℕ}
    (h : ∀ d ∈ P.divisors, |coefficient P d| ≤ 1) (r : DivisorTuple P k) :
    |tupleAmplitude r| ≤ 1 := by sorry

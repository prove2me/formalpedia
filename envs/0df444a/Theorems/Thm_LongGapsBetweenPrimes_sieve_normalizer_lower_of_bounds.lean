-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_sieve_normalizer_lower_of_bounds
-- name    : LongGapsBetweenPrimes.sieve_normalizer_lower_of_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:41:16.627682+00:00
-- url     : https://prove2.me/theorems/544dfcc3-2607-4adc-a4f5-81d3b1d525a5
-- title:
--   Long Gaps Between Primes: sieve normalizer lower of bounds
-- statement:
--   Explicit size bounds ensure ordered cutoffs and a uniform normalizer lower bound.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1687-L1742
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1687-L1742

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.sieve_normalizer_lower_of_bounds {x : ℝ} (hx : 0 < x)
    (hlx : 1 ≤ Real.log x) (hZ : 2 ≤ sieveZ x)
    (hlarge : 7 * Real.exp 6 * (Real.log x) ^ 6 ≤ x)
    (hsmall : 6 * Real.log (Real.log x) + Real.log 7 + 8 ≤ Real.log x / 2) :
    sieveZ x ≤ sieveY x ∧ normalizerLower ≤ normalizer (sieveP x) := by sorry

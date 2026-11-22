-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_eulerProduct_one_le
-- name    : LongGapsBetweenPrimes.eulerProduct_one_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:30:17.48014+00:00
-- url     : https://prove2.me/theorems/40d8a3b2-6a5a-4e5e-b5eb-19f39e72bbe5
-- title:
--   Long Gaps Between Primes: euler Product one le
-- statement:
--   An explicit weak Mertens upper bound, sufficient throughout the proof.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1099-L1123
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1099-L1123

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.eulerProduct_one_le {N : ℕ} (hN : 2 ≤ N) :
    eulerProduct N 1 ≤ Real.exp 6 * (1 + Real.log N) := by sorry

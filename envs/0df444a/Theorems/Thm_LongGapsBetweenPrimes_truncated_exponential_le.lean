-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_truncated_exponential_le
-- name    : LongGapsBetweenPrimes.truncated_exponential_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:46:33.383804+00:00
-- url     : https://prove2.me/theorems/5aeface1-ab78-4a13-8f2a-3537f56a445d
-- title:
--   Long Gaps Between Primes: truncated exponential le
-- statement:
--   The truncation tail is at most `1 / x ^ 3` under the sieve size bounds.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3310-L3316
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3310-L3316

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.truncated_exponential_le {n : ℕ} {x β C : ℝ} (hx : 0 < x) (hβ : 0 ≤ β)
    (hsize : (n : ℝ) * C ≤ x / 16) (hlog : 48 * Real.log x ≤ x * β) :
    sieveD x ^ (-β) * Real.exp ((n : ℝ) * C * β) ≤ 1 / x ^ 3 := by sorry

-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_truncated_double_exponential_le
-- name    : LongGapsBetweenPrimes.truncated_double_exponential_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:46:34.373819+00:00
-- url     : https://prove2.me/theorems/f675709e-1bcb-413e-adf1-7154a7c13933
-- title:
--   Long Gaps Between Primes: truncated double exponential le
-- statement:
--   The truncation tail with doubled exponent is at most `1 / x ^ 6`.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3319-L3325
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3319-L3325

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.truncated_double_exponential_le {n : ℕ} {x β C : ℝ} (hx : 0 < x) (hβ : 0 ≤ β)
    (hsize : (n : ℝ) * C ≤ x / 16) (hlog : 48 * Real.log x ≤ x * β) :
    sieveD x ^ (-(2 * β)) * Real.exp ((n : ℝ) * C * (2 * β)) ≤ 1 / x ^ 6 := by sorry

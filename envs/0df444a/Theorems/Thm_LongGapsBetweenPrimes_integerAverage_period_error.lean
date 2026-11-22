-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_integerAverage_period_error
-- name    : LongGapsBetweenPrimes.integerAverage_period_error
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:42:36.267869+00:00
-- url     : https://prove2.me/theorems/0ce70094-7bb3-44f6-b03f-ecb1dd52c299
-- title:
--   Long Gaps Between Primes: integer Average period error
-- statement:
--   The interval average of a bounded periodic function has error at most `m / T`.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2338-L2342
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2338-L2342

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.integerAverage_period_error {m q T : ℕ} (hm : 0 < m) (hq : 0 < q) (hT : 0 < T)
    (hmq : m ∣ q) (f : ℕ → ℝ) (hperiod : ∀ n, f (n % m) = f n) (hf : ∀ n, |f n| ≤ 1) :
    |integerAverage T f - integerAverage q f| ≤ (m : ℝ) / T := by sorry

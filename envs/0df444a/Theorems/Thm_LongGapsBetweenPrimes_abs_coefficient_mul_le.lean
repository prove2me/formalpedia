-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_abs_coefficient_mul_le
-- name    : LongGapsBetweenPrimes.abs_coefficient_mul_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:39:14.409207+00:00
-- url     : https://prove2.me/theorems/9a8e5ff3-58fb-4618-8d0b-0568a332162a
-- title:
--   Long Gaps Between Primes: abs coefficient mul le
-- statement:
--   Multiplying a nontrivial divisor by a prime decreases the absolute coefficient.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L833-L844
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L833-L844

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.abs_coefficient_mul_le {P p e : ℕ} (hP : 1 < P) (hp : 1 ≤ p) (he : 1 < e) :
    |coefficient P (p * e)| ≤ |coefficient P e| := by sorry

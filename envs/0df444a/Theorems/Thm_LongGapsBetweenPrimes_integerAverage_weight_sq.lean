-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_integerAverage_weight_sq
-- name    : LongGapsBetweenPrimes.integerAverage_weight_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:42:35.9848+00:00
-- url     : https://prove2.me/theorems/d78109a5-d0a8-4aad-90ad-b5307bf13afe
-- title:
--   Long Gaps Between Primes: integer Average weight sq
-- statement:
--   Expand the average of a squared weighted sum into pairwise averages.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2345-L2351
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2345-L2351

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.integerAverage_weight_sq {ι : Type*} [Fintype ι] (T : ℕ) (c : ι → ℝ) (f : ι → ℕ → ℝ) :
    integerAverage T (fun n => (∑ i, c i * f i n) ^ 2) =
      ∑ i, ∑ j, c i * c j * integerAverage T (fun n => f i n * f j n) := by sorry

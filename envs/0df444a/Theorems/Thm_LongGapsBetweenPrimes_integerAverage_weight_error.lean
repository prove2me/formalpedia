-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_integerAverage_weight_error
-- name    : LongGapsBetweenPrimes.integerAverage_weight_error
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:42:49.765801+00:00
-- url     : https://prove2.me/theorems/5971593d-b859-46e2-9ea5-2b7a3d141a37
-- title:
--   Long Gaps Between Primes: integer Average weight error
-- statement:
--   Pairwise average errors give a quadratic error bound for a squared weighted sum.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2354-L2375
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2354-L2375

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.integerAverage_weight_error {ι : Type*} [Fintype ι] (q T : ℕ)
    (c : ι → ℝ) (hc : ∀ i, |c i| ≤ 1) (f : ι → ℕ → ℝ) (E : ℝ)
    (hpair : ∀ i j, |integerAverage T (fun n => f i n * f j n) -
      integerAverage q (fun n => f i n * f j n)| ≤ E) :
    |integerAverage T (fun n => (∑ i, c i * f i n) ^ 2) -
      integerAverage q (fun n => (∑ i, c i * f i n) ^ 2)| ≤ (Fintype.card ι : ℝ) ^ 2 * E := by sorry

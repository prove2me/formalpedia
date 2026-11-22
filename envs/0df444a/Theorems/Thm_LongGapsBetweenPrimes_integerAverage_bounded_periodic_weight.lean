-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_integerAverage_bounded_periodic_weight
-- name    : LongGapsBetweenPrimes.integerAverage_bounded_periodic_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:43:36.675139+00:00
-- url     : https://prove2.me/theorems/0c122b86-5acd-4001-8295-1a513ca123bc
-- title:
--   Long Gaps Between Primes: integer Average bounded periodic weight
-- statement:
--   Bound the second-moment averaging error using the periods and number of summands.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2532-L2559
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2532-L2559

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.integerAverage_bounded_periodic_weight {ι : Type*} [Fintype ι]
    {q T : ℕ} (hq : 0 < q) (hT : 0 < T) {D : ℝ} (hD : 0 ≤ D)
    (period : ι → ℕ) (hperiod_pos : ∀ i, 0 < period i) (hperiod_q : ∀ i, period i ∣ q)
    (hperiod_D : ∀ i, (period i : ℝ) ≤ D)
    (c : ι → ℝ) (hc : ∀ i, |c i| ≤ 1) (f : ι → ℕ → ℝ)
    (hf : ∀ i n, |f i n| ≤ 1) (hmod : ∀ i n, f i (n % period i) = f i n) :
    |integerAverage T (fun n => (∑ i, c i * f i n) ^ 2) -
      integerAverage q (fun n => (∑ i, c i * f i n) ^ 2)| ≤
        (Fintype.card ι : ℝ) ^ 2 * (D ^ 2 / T) := by sorry

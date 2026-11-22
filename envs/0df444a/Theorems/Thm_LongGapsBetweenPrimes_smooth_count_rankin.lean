-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_smooth_count_rankin
-- name    : LongGapsBetweenPrimes.smooth_count_rankin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:47:29.552608+00:00
-- url     : https://prove2.me/theorems/76e64ecb-fd53-464b-95c4-27eb03430bd5
-- title:
--   Long Gaps Between Primes: smooth count rankin
-- statement:
--   A finite Euler-product bound for the count of smooth integers up to `H`.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3814-L3830
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3814-L3830

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.smooth_count_rankin {N H : ℕ} {σ : ℝ} (hσ : 0 < σ)
    (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 H)
    (hsmooth : ∀ n ∈ S, n ∈ (N + 1).smoothNumbers) :
    (S.card : ℝ) ≤ (H : ℝ) ^ σ * eulerProduct N σ := by sorry

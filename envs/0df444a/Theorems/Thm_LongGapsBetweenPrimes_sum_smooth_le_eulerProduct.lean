-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_sum_smooth_le_eulerProduct
-- name    : LongGapsBetweenPrimes.sum_smooth_le_eulerProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:31:05.526002+00:00
-- url     : https://prove2.me/theorems/d652bbcf-c37c-456f-8939-ab95e201d769
-- title:
--   Long Gaps Between Primes: sum smooth le euler Product
-- statement:
--   The weighted sum over smooth numbers is bounded by the finite Euler product.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L977-L990
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L977-L990

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.sum_smooth_le_eulerProduct {N : ℕ} {σ : ℝ} (hσ : 0 < σ)
    (S : Finset ℕ) (hS : ∀ n ∈ S, n ∈ (N + 1).smoothNumbers) :
    (∑ n ∈ S, (n : ℝ) ^ (-σ)) ≤ eulerProduct N σ := by sorry

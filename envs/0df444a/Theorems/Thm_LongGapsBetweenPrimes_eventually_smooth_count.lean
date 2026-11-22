-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_eventually_smooth_count
-- name    : LongGapsBetweenPrimes.eventually_smooth_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:47:55.510152+00:00
-- url     : https://prove2.me/theorems/3270c378-58d8-4cd1-b127-8b67a69a72f7
-- title:
--   Long Gaps Between Primes: eventually smooth count
-- statement:
--   Eventually, at most `H / (log x)^3` integers up to `H` are `coverZ x`-smooth.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3933-L4015
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3933-L4015

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.eventually_smooth_count : ∀ᶠ x : ℝ in Filter.atTop,
    ∀ H : ℕ, x ≤ H → ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 H →
    (∀ n ∈ S, ∀ p : ℕ, p.Prime → p ∣ n → p ≤ coverZ x) →
    (S.card : ℝ) ≤ (H : ℝ) / Real.log x ^ 3 := by sorry

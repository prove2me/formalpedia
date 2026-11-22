-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_short_translates_with_sieveDelta
-- name    : LongGapsBetweenPrimes.short_translates_with_sieveDelta
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:35:43.799286+00:00
-- url     : https://prove2.me/theorems/85447cc5-8b79-451f-8f55-3ca55c8508fa
-- title:
--   Long Gaps Between Primes: short translates with sieve Delta
-- statement:
--   Proposition 1.2, proved with the explicit coefficient construction above.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3612-L3669
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3612-L3669

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.short_translates_with_sieveDelta : ∀ᶠ x : ℝ in Filter.atTop,
    ∀ H : ℕ, x < H → (H : ℝ) ≤ x * (Real.log x) ^ 2 →
    ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 H → (S.card : ℝ) ≤ sieveDelta * x →
    ∀ b : ℕ, b < primorial ⌊x⌋₊ →
    ∃ t : ℕ, 1 ≤ t ∧ (t : ℝ) ≤ Real.exp x ∧
      ∀ s ∈ S, ¬Nat.Prime (b + primorial ⌊x⌋₊ * t + s) := by sorry

-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_product_collision_bound
-- name    : LongGapsBetweenPrimes.product_collision_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:39:10.898802+00:00
-- url     : https://prove2.me/theorems/2a192719-18b5-4f0f-8991-48cb942e6eb9
-- title:
--   Long Gaps Between Primes: product collision bound
-- statement:
--   The collision estimate for independently chosen divisors: a common mark
--   in two coordinates costs at most the square of its one-coordinate mass.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L779-L808
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L779-L808

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.product_collision_bound {α Ω : Type*} [Fintype α] [Fintype Ω]
    (w : Ω → ℝ) (hw : ∀ d, 0 ≤ w d) (hsum : ∑ d, w d = 1)
    (mark : α → Ω → Prop) [∀ p, DecidablePred (mark p)] (k : ℕ) :
    (∑ r : Fin k → Ω, (∏ i, w (r i)) *
      if ∃ p i j, i ≠ j ∧ mark p (r i) ∧ mark p (r j) then 1 else 0) ≤
        (k : ℝ) ^ 2 * ∑ p, (∑ d, w d * if mark p d then 1 else 0) ^ 2 := by sorry

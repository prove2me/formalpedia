-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_abs_productBasis_le_one
-- name    : LongGapsBetweenPrimes.abs_productBasis_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:43:58.824953+00:00
-- url     : https://prove2.me/theorems/f75cc7bd-9e80-4749-8e03-4c26932f6fa2
-- title:
--   Long Gaps Between Primes: abs product Basis le one
-- statement:
--   A product of local basis values bounded by one is bounded by one.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2613-L2617
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2613-L2617

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.abs_productBasis_le_one {α : Type*} [Fintype α] {Ω J : α → Type*}
    (f : (p : α) → J p → Ω p → ℝ) (hf : ∀ p i t, |f p i t| ≤ 1)
    (σ : (p : α) → J p) (t : (p : α) → Ω p) : |productBasis f σ t| ≤ 1 := by sorry

-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_indexed_product_second_moment
-- name    : LongGapsBetweenPrimes.indexed_product_second_moment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:34:27.808796+00:00
-- url     : https://prove2.me/theorems/b5afc029-818b-4050-93b3-5dd939ba4240
-- title:
--   Long Gaps Between Primes: indexed product second moment
-- statement:
--   Row bounds control the second moment of an indexed sum of product basis functions.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2033-L2055
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2033-L2055

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.indexed_product_second_moment {α ι : Type*} [Fintype α] [DecidableEq α]
    [Fintype ι] (size : α → ℕ) (hsize : ∀ p, 1 < size p) {k : ℕ}
    (root : (p : α) → Fin k → Fin (size p)) (hroot : ∀ p, Function.Injective (root p))
    (σ : ι → α → Option (Fin k)) (hσ : Function.Injective σ) (c : ι → ℝ) (ε : ℝ)
    (hbound : ∀ i, (∏ p, localRow (size p) k (σ i p)) - 1 ≤ ε) :
    |Finset.expect Finset.univ (fun t =>
        (∑ i, c i * productBasis (fun p => localBasis (root p)) (σ i) t) ^ 2) -
      ∑ i, c i ^ 2| ≤ ε * ∑ i, c i ^ 2 := by sorry

-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_average_productBasis_localBasis
-- name    : LongGapsBetweenPrimes.average_productBasis_localBasis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:38:46.102507+00:00
-- url     : https://prove2.me/theorems/1955f01e-354d-4549-ac2c-20792f40de86
-- title:
--   Long Gaps Between Primes: average product Basis local Basis
-- statement:
--   Products of local basis functions have Gram kernel `productKernel`.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L629-L643
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L629-L643

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.average_productBasis_localBasis {α : Type*} [Fintype α] [DecidableEq α]
    (size : α → ℕ) (hsize : ∀ p, 1 < size p) {k : ℕ}
    (root : (p : α) → Fin k → Fin (size p)) (hroot : ∀ p, Function.Injective (root p))
    (σ τ : α → Option (Fin k)) :
    Finset.expect Finset.univ (fun t => productBasis (fun p => localBasis (root p)) σ t *
      productBasis (fun p => localBasis (root p)) τ t) = productKernel size σ τ := by sorry

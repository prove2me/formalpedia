-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_assignmentNormalizer_mul_basis
-- name    : LongGapsBetweenPrimes.assignmentNormalizer_mul_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:34:47.268465+00:00
-- url     : https://prove2.me/theorems/8573a8b1-23b7-432a-89e5-3771f31e3b8d
-- title:
--   Long Gaps Between Primes: assignment Normalizer mul basis
-- statement:
--   Multiplying by the assignment normalizer removes the local basis normalization.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2184-L2195
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2184-L2195

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.assignmentNormalizer_mul_basis {α : Type*} [Fintype α] (size : α → ℕ)
    (hsize : ∀ p, 1 < size p) {k : ℕ} (root : (p : α) → Fin k → Fin (size p))
    (σ : α → Option (Fin k)) (t : (p : α) → Fin (size p)) :
    assignmentNormalizer size σ * productBasis (fun p => localBasis (root p)) σ t =
      productBasis (fun p => rawLocalBasis (root p)) σ t := by sorry

-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_sum_abs_productKernel
-- name    : LongGapsBetweenPrimes.sum_abs_productKernel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:38:48.434807+00:00
-- url     : https://prove2.me/theorems/13dc5009-ca2a-473b-a03a-cf3df00a3fb1
-- title:
--   Long Gaps Between Primes: sum abs product Kernel
-- statement:
--   The product of local row sums from the proof of (3.9).
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L620-L626
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L620-L626

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.sum_abs_productKernel {α : Type*} [Fintype α] [DecidableEq α]
    (size : α → ℕ) (hsize : ∀ p, 1 < size p) {k : ℕ} (σ : α → Option (Fin k)) :
    (∑ τ, |productKernel size σ τ|) = ∏ p, localRow (size p) k (σ p) := by sorry

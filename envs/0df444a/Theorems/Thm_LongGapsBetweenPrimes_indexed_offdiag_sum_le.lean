-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_indexed_offdiag_sum_le
-- name    : LongGapsBetweenPrimes.indexed_offdiag_sum_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:41:49.993471+00:00
-- url     : https://prove2.me/theorems/d84f15fd-ef51-4304-bb36-8509b39539cb
-- title:
--   Long Gaps Between Primes: indexed offdiag sum le
-- statement:
--   Injective indexing bounds the row sum away from the diagonal by the full sum minus one.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2016-L2030
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2016-L2030

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.indexed_offdiag_sum_le {ι Λ : Type*} [Fintype ι] [Fintype Λ]
    [DecidableEq ι] (σ : ι → Λ) (hσ : Function.Injective σ)
    (K : Λ → Λ → ℝ) (hdiag : ∀ j, K j j = 1) (i : ι) :
    (∑ j : ι, if j = i then 0 else |K (σ i) (σ j)|) ≤
      (∑ τ : Λ, |K (σ i) τ|) - 1 := by sorry

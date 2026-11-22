-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_sum_pair_marked_product
-- name    : LongGapsBetweenPrimes.sum_pair_marked_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:39:14.383426+00:00
-- url     : https://prove2.me/theorems/27a8d526-ecce-4e77-a3a8-fed60a04c14a
-- title:
--   Long Gaps Between Primes: sum pair marked product
-- statement:
--   Independence of two marked coordinates under a product of normalized masses.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L755-L775
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L755-L775

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.sum_pair_marked_product {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] (w : Ω → ℝ) (hw : ∑ d, w d = 1)
    (mark : Ω → Prop) [DecidablePred mark] (i j : ι) (hij : i ≠ j) :
    (∑ r : ι → Ω, (∏ ℓ, w (r ℓ)) * if mark (r i) ∧ mark (r j) then 1 else 0) =
      (∑ d, w d * if mark d then 1 else 0) ^ 2 := by sorry

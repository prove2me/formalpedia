-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_weighted_union_bound
-- name    : LongGapsBetweenPrimes.weighted_union_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:39:08.519902+00:00
-- url     : https://prove2.me/theorems/2d41ce63-72ef-4a72-bd05-9508d7d5639e
-- title:
--   Long Gaps Between Primes: weighted union bound
-- statement:
--   A weighted union bound, stated without a probability-space interface.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L737-L752
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L737-L752

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.weighted_union_bound {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (w : Ω → ℝ) (event : ι → Ω → Prop) [∀ i, DecidablePred (event i)]
    (hw : ∀ t, 0 ≤ w t) :
    (∑ t, w t * if ∃ i, event i t then 1 else 0) ≤
      ∑ i, ∑ t, w t * if event i t then 1 else 0 := by sorry

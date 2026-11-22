-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_quadratic_form_near_diagonal
-- name    : LongGapsBetweenPrimes.quadratic_form_near_diagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:38:20.510812+00:00
-- url     : https://prove2.me/theorems/e92475a9-62d9-4c0a-9e11-f1645435a39d
-- title:
--   Long Gaps Between Primes: quadratic form near diagonal
-- statement:
--   Row sums away from the diagonal bound the quadratic error from the identity.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L487-L509
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L487-L509

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.quadratic_form_near_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ι → ℝ) (K : ι → ι → ℝ) (ε : ℝ)
    (hsym : ∀ i j, K i j = K j i) (hdiag : ∀ i, K i i = 1)
    (hrow : ∀ i, (∑ j, if j = i then 0 else |K i j|) ≤ ε) :
    |(∑ i, ∑ j, c i * c j * K i j) - ∑ i, c i ^ 2| ≤ ε * ∑ i, c i ^ 2 := by sorry

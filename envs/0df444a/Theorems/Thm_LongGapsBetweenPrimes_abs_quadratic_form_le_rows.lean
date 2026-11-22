-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_abs_quadratic_form_le_rows
-- name    : LongGapsBetweenPrimes.abs_quadratic_form_le_rows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:38:17.831952+00:00
-- url     : https://prove2.me/theorems/24c1ca1c-7068-4fd8-a6ca-a5ffe84e472d
-- title:
--   Long Gaps Between Primes: abs quadratic form le rows
-- statement:
--   A symmetric matrix is controlled by its absolute row sums. This is the
--   2|ab| ≤ a²+b² argument invoked in the proof of (3.9).
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L466-L484
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L466-L484

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.abs_quadratic_form_le_rows {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (K : ι → ι → ℝ) (hK : ∀ i j, |K i j| = |K j i|) :
    |∑ i, ∑ j, c i * c j * K i j| ≤ ∑ i, c i ^ 2 * ∑ j, |K i j| := by sorry

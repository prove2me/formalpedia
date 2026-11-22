-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_sum_residueFactor
-- name    : LongGapsBetweenPrimes.sum_residueFactor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:32:40.295181+00:00
-- url     : https://prove2.me/theorems/5b5f3f15-febc-430d-9379-1f500f0d5ca0
-- title:
--   Long Gaps Between Primes: sum residue Factor
-- statement:
--   The local mean is zero (Section 3.1).
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L133-L136
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L133-L136

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.sum_residueFactor {p : ℕ} (hp : 1 < p) (a : Fin p) :
    ∑ t : Fin p, residueFactor a t = 0 := by sorry

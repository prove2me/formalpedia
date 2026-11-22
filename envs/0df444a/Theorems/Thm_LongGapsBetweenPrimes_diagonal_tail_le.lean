-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_diagonal_tail_le
-- name    : LongGapsBetweenPrimes.diagonal_tail_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:37:24.470599+00:00
-- url     : https://prove2.me/theorems/592ffb6a-2e8a-49ca-ba69-2911b745d3dc
-- title:
--   Long Gaps Between Primes: diagonal tail le
-- statement:
--   The first inequality in (3.10), with no asymptotic assumptions.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L314-L321
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L314-L321

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.diagonal_tail_le (P k : ℕ) {D β : ℝ} (hD : 0 < D) (hβ : 0 ≤ β) :
    (∑ r ∈ (Finset.univ : Finset (DivisorTuple P k)).filter
        (fun r => D < (tupleProduct r : ℝ)), tupleMass r) ≤
      D ^ (-β) * coefficientMoment P β ^ k := by sorry

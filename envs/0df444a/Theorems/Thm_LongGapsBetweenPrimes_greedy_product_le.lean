-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_greedy_product_le
-- name    : LongGapsBetweenPrimes.greedy_product_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:48:00.2238+00:00
-- url     : https://prove2.me/theorems/eebfc669-9401-41a7-96d9-45d8ae812d00
-- title:
--   Long Gaps Between Primes: greedy product le
-- statement:
--   A logarithmic upper bound for the product of greedy survival factors.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L4018-L4038
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L4018-L4038

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.greedy_product_le {W Z : ℕ} (hW : 2 ≤ W) (hWZ : W ≤ Z) :
    (∏ p ∈ auxiliaryPrimes W Z, (1 - 1 / (p : ℝ))) ≤
      Real.exp 6 * (1 + Real.log W) / Real.log Z := by sorry

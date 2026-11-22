-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_eventually_greedy_product_bound
-- name    : LongGapsBetweenPrimes.eventually_greedy_product_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:47:54.426268+00:00
-- url     : https://prove2.me/theorems/31f6a36a-9fd9-414c-a3d7-f9a0882ddbb2
-- title:
--   Long Gaps Between Primes: eventually greedy product bound
-- statement:
--   The chosen cutoffs give an explicit bound for the greedy survival product.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L4041-L4080
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L4041-L4080

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.eventually_greedy_product_bound : ∀ᶠ x : ℝ in Filter.atTop,
    (∏ p ∈ auxiliaryPrimes (coverW x) (coverZ x), (1 - 1 / (p : ℝ))) ≤
      10 * smoothScaleConstant * Real.exp 6 * Real.log (Real.log x) ^ 2 /
        (Real.log x * Real.log (Real.log (Real.log x))) := by sorry

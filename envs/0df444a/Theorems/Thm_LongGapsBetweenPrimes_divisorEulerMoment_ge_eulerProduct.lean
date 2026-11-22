-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_divisorEulerMoment_ge_eulerProduct
-- name    : LongGapsBetweenPrimes.divisorEulerMoment_ge_eulerProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:40:03.911596+00:00
-- url     : https://prove2.me/theorems/da6786a3-aecc-48bc-bc9a-2e9ef1b5436c
-- title:
--   Long Gaps Between Primes: divisor Euler Moment ge euler Product
-- statement:
--   A lower bound for the squarefree-divisor Euler product by a usual Euler product.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1228-L1242
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1228-L1242

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.divisorEulerMoment_ge_eulerProduct {Z Y : ℕ} (hZY : Z ≤ Y) {t : ℝ} (ht : 0 < t) :
    eulerProduct Y (1 + t) ≤
      divisorEulerMoment (auxiliaryProduct Z Y) (-t) * eulerProduct Z (1 + t) := by sorry

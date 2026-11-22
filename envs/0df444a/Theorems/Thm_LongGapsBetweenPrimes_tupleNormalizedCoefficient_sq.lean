-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_tupleNormalizedCoefficient_sq
-- name    : LongGapsBetweenPrimes.tupleNormalizedCoefficient_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:34:52.975969+00:00
-- url     : https://prove2.me/theorems/4fdcfa0a-c909-47bb-90eb-5f66f80a8093
-- title:
--   Long Gaps Between Primes: tuple Normalized Coefficient sq
-- statement:
--   A normalized tuple coefficient has square equal to its diagonal mass.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2228-L2235
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2228-L2235

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.tupleNormalizedCoefficient_sq {P k : ℕ} (hP : Squarefree P) (r : DivisorTuple P k)
    (hpair : ∀ i j, i ≠ j → Nat.Coprime (r i).val (r j).val) :
    tupleNormalizedCoefficient r ^ 2 = tupleMass r := by sorry

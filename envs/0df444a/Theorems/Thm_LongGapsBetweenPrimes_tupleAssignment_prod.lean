-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_tupleAssignment_prod
-- name    : LongGapsBetweenPrimes.tupleAssignment_prod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:34:38.630477+00:00
-- url     : https://prove2.me/theorems/b7186d1b-87af-4504-a5f2-0d8264cb2912
-- title:
--   Long Gaps Between Primes: tuple Assignment prod
-- statement:
--   Regroup a product over assigned primes by tuple coordinates.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2110-L2120
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2110-L2120

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.tupleAssignment_prod {P k : ℕ} {M : Type*} [CommMonoid M]
    (r : DivisorTuple P k) (hpair : ∀ i j, i ≠ j → Nat.Coprime (r i).val (r j).val)
    (f : PrimeIndex P → Fin k → M) :
    (∏ p : PrimeIndex P, match tupleAssignment r p with | none => 1 | some i => f p i) =
      ∏ i, ∏ p : PrimeIndex P, if p.val ∣ (r i).val then f p i else 1 := by sorry

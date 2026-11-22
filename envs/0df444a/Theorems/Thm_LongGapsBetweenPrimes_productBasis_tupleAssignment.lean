-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_productBasis_tupleAssignment
-- name    : LongGapsBetweenPrimes.productBasis_tupleAssignment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:35:17.563804+00:00
-- url     : https://prove2.me/theorems/b4c88c1e-656c-4923-af58-3a7947fb8b0d
-- title:
--   Long Gaps Between Primes: product Basis tuple Assignment
-- statement:
--   Factor a tuple's product basis function over its coordinates.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2772-L2783
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2772-L2783

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.productBasis_tupleAssignment {P k : ℕ}
    (f : (p : PrimeIndex P) → Option (Fin k) → Fin p.val → ℝ)
    (hf : ∀ p t, f p none t = 1) (r : DivisorTuple P k)
    (hr : ∀ i j, i ≠ j → Nat.Coprime (r i).val (r j).val)
    (t : (p : PrimeIndex P) → Fin p.val) :
    productBasis f (tupleAssignment r) t = ∏ i, coordinateBasis f (r i) i t := by sorry

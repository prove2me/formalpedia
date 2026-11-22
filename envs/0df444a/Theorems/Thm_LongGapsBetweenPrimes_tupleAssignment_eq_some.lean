-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_tupleAssignment_eq_some
-- name    : LongGapsBetweenPrimes.tupleAssignment_eq_some
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:34:30.168914+00:00
-- url     : https://prove2.me/theorems/813a0ace-451b-4817-a04e-28b1652c34b9
-- title:
--   Long Gaps Between Primes: tuple Assignment eq some
-- statement:
--   In a pairwise coprime tuple, a prime is assigned exactly to the coordinate it divides.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2073-L2086
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2073-L2086

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.tupleAssignment_eq_some {P k : ℕ} (r : DivisorTuple P k)
    (hpair : ∀ i j, i ≠ j → Nat.Coprime (r i).val (r j).val)
    (p : PrimeIndex P) (i : Fin k) : tupleAssignment r p = some i ↔ p.val ∣ (r i).val := by sorry

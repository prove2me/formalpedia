-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_tuplePairwise_insertNth
-- name    : LongGapsBetweenPrimes.tuplePairwise_insertNth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:44:24.990916+00:00
-- url     : https://prove2.me/theorems/003efa94-d4c2-4892-bf50-e6eb1d5659f0
-- title:
--   Long Gaps Between Primes: tuple Pairwise insert Nth
-- statement:
--   Insertion preserves pairwise coprimality iff the new divisor is coprime to the rest.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2709-L2716
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2709-L2716

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.tuplePairwise_insertNth {P k : ℕ} (i : Fin (k + 1)) (d : DivisorIndex P)
    (r : DivisorTuple P k) :
    (∀ j l, j ≠ l →
      Nat.Coprime (i.insertNth (α := fun _ => DivisorIndex P) d r j).val
        (i.insertNth (α := fun _ => DivisorIndex P) d r l).val) ↔
      (∀ j l, j ≠ l → Nat.Coprime (r j).val (r l).val) ∧ d.val.Coprime (tupleProduct r) := by sorry

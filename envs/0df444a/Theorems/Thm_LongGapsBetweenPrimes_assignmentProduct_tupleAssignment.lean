-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_assignmentProduct_tupleAssignment
-- name    : LongGapsBetweenPrimes.assignmentProduct_tupleAssignment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:30:36.993645+00:00
-- url     : https://prove2.me/theorems/b714a744-32b9-473f-a2e6-c9764379a6fa
-- title:
--   Long Gaps Between Primes: assignment Product tuple Assignment
-- statement:
--   The product of assigned primes equals the tuple product for squarefree `P`.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2146-L2154
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2146-L2154

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.assignmentProduct_tupleAssignment {P k : ℕ} (hP : Squarefree P) (r : DivisorTuple P k)
    (hpair : ∀ i j, i ≠ j → Nat.Coprime (r i).val (r j).val) :
    assignmentProduct (fun p : PrimeIndex P => p.val) (tupleAssignment r) = tupleProduct r := by sorry

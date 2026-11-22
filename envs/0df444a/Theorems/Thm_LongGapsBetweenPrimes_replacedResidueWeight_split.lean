-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_replacedResidueWeight_split
-- name    : LongGapsBetweenPrimes.replacedResidueWeight_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:44:49.524681+00:00
-- url     : https://prove2.me/theorems/f8ba721b-f03c-4502-98bb-f8bb5a495a7e
-- title:
--   Long Gaps Between Primes: replaced Residue Weight split
-- statement:
--   Split the replaced weight into smaller tuples and coefficient remainders.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2828-L2840
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2828-L2840

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.replacedResidueWeight_split {P k : ℕ} (hP : Squarefree P) (D : ℝ)
    (root : (p : PrimeIndex P) → Fin (k + 1) → Fin p.val) (i : Fin (k + 1))
    (t : (p : PrimeIndex P) → Fin p.val) :
    replacedResidueWeight P (k + 1) D root i t =
      ∑ r ∈ tupleRegion P k D, coefficientRemainder P (tupleProduct r) D *
        ∏ j, coefficient P (r j).val *
          coordinateBasis (fun p => rawLocalBasis (fun j => root p (i.succAbove j))) (r j) j t := by sorry

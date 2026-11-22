-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_weightedResidueWeight_eq_sum
-- name    : LongGapsBetweenPrimes.weightedResidueWeight_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:45:13.144588+00:00
-- url     : https://prove2.me/theorems/25754072-b802-4a62-9532-1bdb7bc87e56
-- title:
--   Long Gaps Between Primes: weighted Residue Weight eq sum
-- statement:
--   Expand the weighted residue sum as a product over tuple coordinates.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2996-L3009
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2996-L3009

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.weightedResidueWeight_eq_sum {P k : ℕ} (D : ℝ)
    (root : (p : PrimeIndex P) → Fin k → Fin p.val) (b : DivisorTuple P k → ℝ)
    (t : (p : PrimeIndex P) → Fin p.val) :
    weightedResidueWeight P k D root b t =
      ∑ r ∈ tupleRegion P k D, b r *
        ∏ i, coefficient P (r i).val *
          coordinateBasis (fun p => rawLocalBasis (root p)) (r i) i t := by sorry

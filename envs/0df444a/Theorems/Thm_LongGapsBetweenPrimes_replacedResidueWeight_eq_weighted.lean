-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_replacedResidueWeight_eq_weighted
-- name    : LongGapsBetweenPrimes.replacedResidueWeight_eq_weighted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:45:23.137017+00:00
-- url     : https://prove2.me/theorems/195384a0-663f-43a3-b735-b0bdee235439
-- title:
--   Long Gaps Between Primes: replaced Residue Weight eq weighted
-- statement:
--   A replaced weight is a weight on smaller tuples with coefficient-remainder factors.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3051-L3057
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3051-L3057

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.replacedResidueWeight_eq_weighted {P k : ℕ} (hP : Squarefree P) (D : ℝ)
    (root : (p : PrimeIndex P) → Fin (k + 1) → Fin p.val) (i : Fin (k + 1))
    (t : (p : PrimeIndex P) → Fin p.val) :
    replacedResidueWeight P (k + 1) D root i t =
      weightedResidueWeight P k D (fun p j => root p (i.succAbove j))
        (fun r => coefficientRemainder P (tupleProduct r) D) t := by sorry

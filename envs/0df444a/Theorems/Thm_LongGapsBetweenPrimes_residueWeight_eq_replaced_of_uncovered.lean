-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_residueWeight_eq_replaced_of_uncovered
-- name    : LongGapsBetweenPrimes.residueWeight_eq_replaced_of_uncovered
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:45:44.82101+00:00
-- url     : https://prove2.me/theorems/03902d23-7a4b-4d3b-bcbf-11a84d4f99ad
-- title:
--   Long Gaps Between Primes: residue Weight eq replaced of uncovered
-- statement:
--   Avoiding one coordinate's roots makes the original and replaced weights equal.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3131-L3142
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3131-L3142

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.residueWeight_eq_replaced_of_uncovered {P k : ℕ} (D : ℝ)
    (root : (p : PrimeIndex P) → Fin k → Fin p.val) (i : Fin k)
    (t : (p : PrimeIndex P) → Fin p.val) (hi : ∀ p, t p ≠ root p i) :
    residueWeight P k D root t = replacedResidueWeight P k D root i t := by sorry

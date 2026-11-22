-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_integerAverage_residues
-- name    : LongGapsBetweenPrimes.integerAverage_residues
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:43:36.764577+00:00
-- url     : https://prove2.me/theorems/f85cb767-8b2f-46eb-b363-48f03f0bd402
-- title:
--   Long Gaps Between Primes: integer Average residues
-- statement:
--   The Chinese remainder theorem identifies a full-period average with a product average.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2567-L2593
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2567-L2593

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
open scoped Fin.CommRing

theorem LongGapsBetweenPrimes.integerAverage_residues {P : ℕ} (hP : Squarefree P)
    (f : ((p : PrimeIndex P) → Fin p.val) → ℝ) :
    integerAverage P (fun n => f (residueVector P n)) = Finset.expect Finset.univ f := by sorry

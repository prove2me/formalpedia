-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_basisWeight_eq_tupleSum
-- name    : LongGapsBetweenPrimes.basisWeight_eq_tupleSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:44:33.337119+00:00
-- url     : https://prove2.me/theorems/710a57bd-3d84-4209-8359-455eee003e76
-- title:
--   Long Gaps Between Primes: basis Weight eq tuple Sum
-- statement:
--   Expand a basis weight as a sum of products over tuple coordinates.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2786-L2796
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2786-L2796

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.basisWeight_eq_tupleSum {P k : ℕ} (D : ℝ)
    (f : (p : PrimeIndex P) → Option (Fin k) → Fin p.val → ℝ)
    (hf : ∀ p t, f p none t = 1) (t : (p : PrimeIndex P) → Fin p.val) :
    basisWeight P k D f t =
      ∑ r ∈ tupleRegion P k D, ∏ i, coefficient P (r i).val * coordinateBasis f (r i) i t := by sorry

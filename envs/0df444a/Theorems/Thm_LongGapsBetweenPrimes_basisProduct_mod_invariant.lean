-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_basisProduct_mod_invariant
-- name    : LongGapsBetweenPrimes.basisProduct_mod_invariant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:44:04.6847+00:00
-- url     : https://prove2.me/theorems/9fa0376d-64b5-46ea-8576-416c16a0e409
-- title:
--   Long Gaps Between Primes: basis Product mod invariant
-- statement:
--   A product basis function depends only on the residue modulo its assignment product.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2634-L2647
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2634-L2647

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.basisProduct_mod_invariant {P k : ℕ}
    (f : (p : PrimeIndex P) → Option (Fin k) → Fin p.val → ℝ)
    (hf : ∀ p t, f p none t = 1) (σ : PrimeIndex P → Option (Fin k)) (n : ℕ) :
    productBasis f σ (residueVector P (n % assignmentProduct (fun p : PrimeIndex P => p.val) σ)) =
      productBasis f σ (residueVector P n) := by sorry

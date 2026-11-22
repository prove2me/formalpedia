-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_assignmentCode_determines
-- name    : LongGapsBetweenPrimes.assignmentCode_determines
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:43:24.96741+00:00
-- url     : https://prove2.me/theorems/6f23e24f-6f62-4936-92f7-058b5d6f9e2e
-- title:
--   Long Gaps Between Primes: assignment Code determines
-- statement:
--   Distinct local roots make the modulus and residue code determine the assignment.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2466-L2486
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2466-L2486

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.assignmentCode_determines {P k : ℕ} (root : (p : PrimeIndex P) → Fin k → Fin p.val)
    (hroot : ∀ p, Function.Injective (root p)) (σ τ : PrimeIndex P → Option (Fin k))
    (hn : assignmentProduct (fun p : PrimeIndex P => p.val) σ =
      assignmentProduct (fun p : PrimeIndex P => p.val) τ)
    (ha : assignmentCode root σ = assignmentCode root τ) : σ = τ := by sorry

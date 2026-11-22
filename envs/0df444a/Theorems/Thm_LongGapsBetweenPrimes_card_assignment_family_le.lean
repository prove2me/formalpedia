-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_card_assignment_family_le
-- name    : LongGapsBetweenPrimes.card_assignment_family_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:43:30.806327+00:00
-- url     : https://prove2.me/theorems/26565390-98c3-4fcb-92a3-c79f8130d0d8
-- title:
--   Long Gaps Between Primes: card assignment family le
-- statement:
--   Encoding an assignment by its modulus and one CRT residue bounds its count.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2489-L2513
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2489-L2513

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.card_assignment_family_le {P k : ℕ} {ι : Type*} [Fintype ι]
    (root : (p : PrimeIndex P) → Fin k → Fin p.val) (hroot : ∀ p, Function.Injective (root p))
    (σ : ι → PrimeIndex P → Option (Fin k)) (hσ : Function.Injective σ)
    {D : ℝ} (hD : 1 ≤ D)
    (hcut : ∀ i, (assignmentProduct (fun p : PrimeIndex P => p.val) (σ i) : ℝ) ≤ D) :
    (Fintype.card ι : ℝ) ≤ 4 * D ^ 2 := by sorry

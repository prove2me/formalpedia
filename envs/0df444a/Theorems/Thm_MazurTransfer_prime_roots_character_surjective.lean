-- Prove2me | Theorems.Thm_MazurTransfer_prime_roots_character_surjective
-- name    : MazurTransfer.prime_roots_character_surjective
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-14T21:53:26.259556+00:00
-- url     : https://prove2.me/theorems/15d1fbb7-aa35-4128-8480-a0902a4fa279
-- title:
--   A nontrivial character into prime roots of unity is surjective
-- statement:
--   Let K be a field, G a group and p a prime. A group homomorphism from G to the p-th roots of unity in K is surjective if it has a value different from one. This result supplies the surjectivity of actual cyclotomic quotient maps constructed from the order-13 Picard pairing.
-- source:
--   Owned MazurTheorem integration, Apache-2.0: PrimeRootsCharacterSurjectivity.surjective_of_exists_ne_one. Uses Mathlib at exact pin 0df444a360eaa60ab8c11dca51a86af692955474, IsPrimitiveRoot.iff_orderOf and IsPrimitiveRoot.eq_pow_of_mem_rootsOfUnity in Mathlib/RingTheory/RootsOfUnity/PrimitiveRoots.lean, and orderOf_eq_prime in Mathlib/GroupTheory/OrderOfElement.lean.

import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

theorem MazurTransfer.prime_roots_character_surjective
    (K G : Type*) [Field K] [Group G] (p : ℕ) [Fact p.Prime] [NeZero p]
    (f : G →* rootsOfUnity p K) (h : ∃ a : G, f a ≠ 1) : Function.Surjective f := by sorry

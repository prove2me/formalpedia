-- Prove2me | Theorems.Thm_GoldbachSieve_witnesses_cover_finset
-- name    : GoldbachSieve.witnesses_cover_finset
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-25T13:29:00.33977+00:00
-- url     : https://prove2.me/theorems/64ef526d-4e30-44bb-a856-527deb0ae5eb
-- title:
--   Witnesses imply sieve pair-sum coverage
-- statement:
--   Let A be a finite set of natural numbers. Suppose each n in A can be written as n = p + q, where p is a prime at most smallBound and q belongs to the specified sieve survivor set. Then A is contained in pairSums, the union of all such prime-plus-survivor sums. This reusable lemma separates the set-theoretic conversion from the blockwise certificate computation.
-- source:
--   Generic set-theoretic bridge for the GoldbachSieve pairSums interface.

import Definitions.Def_GoldbachSieve

namespace GoldbachSieve

theorem witnesses_cover_finset (A : Finset ℕ) (smallBound lo hi cutoff : ℕ)
    (hw : ∀ n ∈ A,
      ∃ p ∈ ((Finset.Icc 2 smallBound).filter Nat.Prime),
        ∃ q ∈ GoldbachSieve.survivors lo hi cutoff, n = p + q) :
    A ⊆ GoldbachSieve.pairSums smallBound lo hi cutoff := by sorry
end GoldbachSieve

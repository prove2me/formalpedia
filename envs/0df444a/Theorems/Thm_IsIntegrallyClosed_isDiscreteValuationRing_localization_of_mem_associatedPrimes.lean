-- Prove2me | Theorems.Thm_IsIntegrallyClosed_isDiscreteValuationRing_localization_of_mem_associatedPrimes
-- name    : IsIntegrallyClosed.isDiscreteValuationRing_localization_of_mem_associatedPrimes
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/f1358b00-fe47-5e20-bb3d-c1d59aad3c8f
-- title:
--   Associated primes of a principal ideal give discrete valuation rings
-- statement:
--   Let $B$ be a commutative ring which is a Noetherian integral domain and is integrally closed in its field of fractions, let $x \in B$ be nonzero, and let $P \subseteq B$ be a prime ideal. Assume that $P$ belongs to $\operatorname{Ass}_B(B/xB)$, i.e. $P$ is an associated prime of the $B$-module $B \,/\, \mathrm{span}\{x\}$ in Mathlib's sense: $P$ is prime and there is an element $z$ of $B/xB$ with $P$ equal to the annihilator of $z$. Then the localisation of $B$ at $P$, realised as `Localization.AtPrime P`, is a discrete valuation ring, i.e. a local principal ideal domain which is not a field.
--
--   This is the classical statement that the prime divisors of a nonzero principal ideal in a Noetherian normal domain are exactly the primes at which the localisation is a discrete valuation ring (one half of Krull's characterisation of normality by the intersection of the localisations at height-one primes). It is used in the project to show that such associated primes have height one, and in the analysis of the integral models of curves, where reducedness and primality of principal ideals at points of a valuation subring are deduced from it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsIntegrallyClosed_isDiscreteValuationRing_localization_of_mem_associatedPrimes.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem IsIntegrallyClosed.isDiscreteValuationRing_localization_of_mem_associatedPrimes
    {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B]
    {x : B} (hx : x ≠ 0) (P : Ideal B) [P.IsPrime]
    (hP : P ∈ associatedPrimes B (B ⧸ Ideal.span {x})) :
    IsDiscreteValuationRing (Localization.AtPrime P) := by sorry

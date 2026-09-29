-- Prove2me | Theorems.Thm_IsIntegrallyClosed_exists_valuationSubring_mem_iff_of_height_eq_one
-- name    : IsIntegrallyClosed.exists_valuationSubring_mem_iff_of_height_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/feaf4526-62b7-5a82-b319-5ded267b42c3
-- title:
--   Localisation at a height-one prime as a valuation subring of K
-- statement:
--   Let $R$ be a commutative ring that is a noetherian integrally closed domain, and let $K$ be a field equipped with an $R$-algebra structure making it a fraction field of $R$. Let $p \subseteq R$ be a prime ideal whose height equals $1$. Then there exists a valuation subring $V$ of $K$ such that: $V$ is a principal ideal ring; $V$ is not the whole of $K$ (i.e. $V \neq \top$ as a valuation subring); and for every $x \in K$, membership $x \in V$ holds if and only if there are $r, s \in R$ with $s \notin p$ and $x \cdot \iota(s) = \iota(r)$, where $\iota =$ `algebraMap R K`. Thus $V$ is exactly the set of fractions in $K$ admitting a denominator outside $p$, i.e. the image of $R_p$ inside $K$, and the statement records that this subring is a proper valuation subring of $K$ which is a principal ideal ring (hence a discrete valuation ring, since it is a local domain that is not a field).
--
--   This is the $R_1$ half of Serre's normality criterion — for a noetherian normal domain, the localisation at a height-one prime is a discrete valuation ring — transported from the abstract localisation into the fraction field in the membership form used by consumers working inside a fixed ambient field. It is cited in the reconstruction of $R$ as the intersection of the valuation subrings attached to its height-one primes, and in the unramifiedness arguments for the local rings of modular curves at height-one primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsIntegrallyClosed_exists_valuationSubring_mem_iff_of_height_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem IsIntegrallyClosed.exists_valuationSubring_mem_iff_of_height_eq_one
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (p : Ideal R) [p.IsPrime] (hp : p.height = 1) :
    ∃ V : ValuationSubring K, IsPrincipalIdealRing V ∧ V ≠ ⊤ ∧
      ∀ x : K, x ∈ V ↔ ∃ r s : R, s ∉ p ∧ x * algebraMap R K s = algebraMap R K r := by sorry

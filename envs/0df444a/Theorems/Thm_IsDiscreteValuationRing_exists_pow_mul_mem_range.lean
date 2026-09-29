-- Prove2me | Theorems.Thm_IsDiscreteValuationRing_exists_pow_mul_mem_range
-- name    : IsDiscreteValuationRing.exists_pow_mul_mem_range
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/d0d88e75-aa5d-5610-a261-062467a483b0
-- title:
--   Powers of a non-unit clear denominators over a discrete valuation ring
-- statement:
--   Let $R$ be a commutative ring which is a domain and a discrete valuation ring, and let $K$ be a field equipped with an $R$-algebra structure making it a fraction field of $R$ (i.e. the structure map $R \to K$ exhibits $K$ as the localisation of $R$ at its non-zero-divisors). Let $t \in R$ be non-zero and lie in the maximal ideal of the local ring $R$, and let $x \in K$ be arbitrary. The assertion is that there exist a natural number $N$ and an element $r \in R$ such that, in $K$, the image of $r$ equals the image of $t$ raised to the $N$-th power times $x$; that is, $t^N x$ lies in the image of $R$ in $K$. Note the quantifier order: $N$ is allowed to depend on $x$, and no bound on $N$ nor uniqueness of $r$ is claimed.
--
--   This is the standard statement that in a discrete valuation ring any non-zero non-unit $t$ generates a denominator-clearing family of powers, so that $K = \bigcup_N t^{-N} R$. It is used in the analysis of integrality at points of modular curves, where at each of the finitely many height-one primes in question the localisation is a discrete valuation ring and a power of a local parameter clears the poles of a given function; the three citing results concern integrality of localised modular functions and the prolongation of places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDiscreteValuationRing_exists_pow_mul_mem_range.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsDiscreteValuationRing.exists_pow_mul_mem_range
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (t : R) (ht : t ≠ 0) (ht' : t ∈ IsLocalRing.maximalIdeal R) (x : K) :
    ∃ N : ℕ, ∃ r : R, algebraMap R K r = algebraMap R K t ^ N * x := by sorry

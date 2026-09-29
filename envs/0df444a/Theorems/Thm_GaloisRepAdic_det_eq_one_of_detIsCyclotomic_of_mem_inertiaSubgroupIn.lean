-- Prove2me | Theorems.Thm_GaloisRepAdic_det_eq_one_of_detIsCyclotomic_of_mem_inertiaSubgroupIn
-- name    : GaloisRepAdic.det_eq_one_of_detIsCyclotomic_of_mem_inertiaSubgroupIn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/904be62a-f98c-5d84-9fd3-8fa746f5a95d
-- title:
--   Cyclotomic determinant is trivial on inertia at q ≠ p
-- statement:
--   Let $A$ be a commutative local Noetherian ring with maximal ideal $\mathfrak m$, and let $\rho$ be a [`GaloisRepAdic`](def/GaloisRep_Adic.html#L16) over $A$: a finite free $A$-module $V$ of rank $2$ together with a monoid homomorphism $\rho.\rho$ from the group of $\mathbb Q$-algebra automorphisms of $\mathrm{AlgebraicClosure}\,\mathbb Q$ into $\mathrm{End}_A(V)$ satisfying the adic continuity condition that for each $n$ there is a finite extension $L/\mathbb Q$ inside $\mathrm{AlgebraicClosure}\,\mathbb Q$ with $\rho(\sigma)v - v \in \mathfrak m^n \cdot V$ for all $v$ and all $\sigma$ fixing $L$ pointwise. Assume $\rho$ has cyclotomic determinant at a prime $p$ in the integral sense of `DetIsCyclotomic`: $p \in \mathfrak m$, and for all $n \in \mathbb N$, all $\sigma$ and all $a \in \mathbb N$ such that $\sigma\mu = \mu^a$ for every $\mu$ with $\mu^{p^n} = 1$, one has $\det \rho(\sigma) - a \in (p^n)A$. Let $q$ be a prime with $q \neq p$, let $p$ be prime, and let $P$ be a valuation subring of $\mathrm{AlgebraicClosure}\,\mathbb Q$ lying over $q$ in the sense that $q$ is a nonunit of $P$. Then for every $\sigma$ in the image in the full automorphism group of the inertia subgroup of the decomposition group of $P$ over $\mathbb Q$, the determinant of $\rho.\rho\,\sigma$ equals $1$.
--
--   This is the determinant computation underlying the shape of the local condition at an auxiliary (Taylor–Wiles) prime $q \neq p$: inertia at $q$ acts with trivial determinant, so that the two tame characters occurring there are mutually inverse. It is used in the construction of inertia characters for representations with cyclotomic determinant, in the unipotence statement for Hecke-ring representations at auxiliary primes, and in the newform-to-Galois-representation statement comparing inertial characteristic polynomials with the cyclotomic character.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_det_eq_one_of_detIsCyclotomic_of_mem_inertiaSubgroupIn.lean

import Mathlib
import Definitions.Def_GaloisRep_Adic
import Definitions.Def_GaloisRep_LocalConditions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IsLocalRing

theorem GaloisRepAdic.det_eq_one_of_detIsCyclotomic_of_mem_inertiaSubgroupIn
    {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (ρ : GaloisRepAdic A) {p : ℕ}
    (hdet : ρ.DetIsCyclotomic p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) (hp : p.Prime)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ P.inertiaSubgroupIn ℚ) :
    LinearMap.det (ρ.ρ σ) = 1 := by sorry

-- Prove2me | Theorems.Thm_GaloisRep_isDeformationCondition_strictOrdinaryCondition_and_isUnipotentOnInertiaAt
-- name    : GaloisRep.isDeformationCondition_strictOrdinaryCondition_and_isUnipotentOnInertiaAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/97fc91ea-64b4-501b-af66-b3a75b6234e3
-- title:
--   Strict ordinary plus unipotent inertia on U is a deformation condition
-- statement:
--   Let $\mathcal O$ be a commutative local ring, $p$ a prime with $p \neq 2$, and $S, U$ finite sets of natural numbers. Consider the predicate which, for a local $\mathcal O$-algebra $A$, assigns to a representation $\rho \in$ [`GaloisRepAdic A`](def/GaloisRep_Adic.html#L16) (a free $A$-module $V$ of rank $2$ with an adically continuous action of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$, realised as the $\mathbb Q$-algebra automorphisms of `AlgebraicClosure ℚ`) the conjunction of: (i) [`GaloisRep.strictOrdinaryCondition 𝒪 p S ρ`](def/GaloisRep_StrictOrdinary.html#L28), i.e. $p$ lies in the maximal ideal of $A$ and for all $n$, all $\sigma$ and all $a$ with $\sigma\mu = \mu^a$ on all $p^n$-th roots of unity one has $\det \rho(\sigma) - a \in (p^n)$, together with the predicate `IsStrictOrdinaryAt` at $p$ and unramifiedness at every prime $q \notin S$; and (ii) for every $q \in U$ with $q$ prime and $q \neq p$, the condition that for each valuation subring $P$ of $\overline{\mathbb Q}$ in which $q$ is a non-unit and each $\sigma$ in the image of the inertia subgroup of $P$, the characteristic polynomial of $\rho(\sigma)$ is $(X-1)^2$. The theorem asserts that this predicate is a deformation condition in the sense of [`GaloisRep.IsDeformationCondition`](def/GaloisRep_DeformationCondition.html#L19): it is invariant under equivalence of representations over Artinian test algebras (local $\mathcal O$-algebras that are Artinian, with local structure map inducing a surjection on residue fields), stable under base change along local $\mathcal O$-algebra maps of test algebras, descends along injective such maps and along fibre-product diagrams of test algebras, and, for a complete noetherian local $\mathcal O$-algebra $A$ with local structure map and surjective induced map on residue fields, holds for $\rho$ precisely when it holds for every base change of $\rho$ along a surjection of $A$ onto an Artinian test algebra.
--
--   This is the verification that the strict ordinary deformation problem — strict ordinariness at $p$ with prescribed ramification outside $S$, reinforced by unipotent inertia at the auxiliary primes in $U$ — satisfies the axioms needed to produce a universal deformation ring. It is used by [`GaloisRep.nonempty_deformationRingData_strictOrdinaryCondition_and_isUnipotentOnInertiaAt`](thm.html#GaloisRep.nonempty_deformationRingData_strictOrdinaryCondition_and_isUnipotentOnInertiaAt), which supplies the deformation rings at the Taylor–Wiles levels obtained by adding primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_isDeformationCondition_strictOrdinaryCondition_and_isUnipotentOnInertiaAt.lean

import Mathlib
import Definitions.Def_GaloisRep_DeformationCondition
import Definitions.Def_GaloisRep_StrictOrdinary

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem GaloisRep.isDeformationCondition_strictOrdinaryCondition_and_isUnipotentOnInertiaAt
    (𝒪 : Type) [CommRing 𝒪] {p : ℕ} {S U : Finset ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    GaloisRep.IsDeformationCondition 𝒪
      (fun _A _ _ _ ρ => GaloisRep.strictOrdinaryCondition 𝒪 p S ρ ∧
        ∀ q ∈ U, q.Prime → q ≠ p → ρ.IsUnipotentOnInertiaAt q) := by sorry

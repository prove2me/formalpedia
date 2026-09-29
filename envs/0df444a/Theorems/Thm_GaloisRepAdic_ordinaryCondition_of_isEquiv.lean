-- Prove2me | Theorems.Thm_GaloisRepAdic_ordinaryCondition_of_isEquiv
-- name    : GaloisRepAdic.ordinaryCondition_of_isEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/8008d4ba-209b-50eb-82e4-e165fbc70af0
-- title:
--   Invariance of the ordinary condition under equivalence
-- statement:
--   Let $A$ be a commutative local ring, let $\mathcal O$ be a commutative ring making $A$ an $\mathcal O$-algebra, and let $\rho_1,\rho_2$ be objects of [`GaloisRepAdic A`](def/GaloisRep_Adic.html#L16): each consists of a free finite $A$-module $V$ with $\operatorname{finrank}_A V = 2$ together with a monoid homomorphism $\rho$ from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$, realised as the $\mathbb Q$-algebra automorphisms of `AlgebraicClosure ℚ`, into $\operatorname{End}_A V$, subject to the adic continuity requirement that for every $n$ there be a finite extension $L/\mathbb Q$ inside $\overline{\mathbb Q}$ with $\rho(\sigma)v - v \in \mathfrak m_A^{\,n}\cdot V$ for all $\sigma$ fixing $L$ pointwise and all $v \in V$. Assume `ρ₁.IsEquiv ρ₂`, i.e. there exists an $A$-linear isomorphism $\rho_1.V \to \rho_2.V$ intertwining the two actions. Let $p$ be a natural number and $S$ a finite set of natural numbers, and suppose $\rho_1$ satisfies [`GaloisRep.ordinaryCondition 𝒪 p S`](def/GaloisRep_LocalConditions.html#L28): the image of $p$ lies in $\mathfrak m_A$ and for all $n$, $\sigma$ and $a$ with $\sigma\mu = \mu^a$ on all $p^n$-th roots of unity one has $\det \rho_1(\sigma) - a \in p^nA$; for every valuation subring of $\overline{\mathbb Q}$ lying over $p$ there is an $A$-line $L$ spanned by the first vector of some basis indexed by `Fin 2`, stable under the decomposition subgroup, with $\rho_1(\sigma)v - v \in L$ for all inertia elements $\sigma$ and all $v$; and for every prime $q \notin S$ and every valuation subring lying over $q$, $\rho_1(\sigma) = 1$ for all $\sigma$ in the inertia subgroup. Then $\rho_2$ satisfies [`GaloisRep.ordinaryCondition 𝒪 p S`](def/GaloisRep_LocalConditions.html#L28) as well.
--
--   This records that the ordinary local condition of type $S$ is a deformation condition in Mazur's sense, being invariant under equivalence of rank-two representations, so that it cuts out a subfunctor of the deformation functor. It is used in the construction of patching data and in the identification of the local Hecke algebra with the corresponding ordinary deformation ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_ordinaryCondition_of_isEquiv.lean

import Definitions.Def_GaloisRep_LocalConditions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem GaloisRepAdic.ordinaryCondition_of_isEquiv
    {A : Type} [CommRing A] [IsLocalRing A]
    (𝒪 : Type) [CommRing 𝒪] [Algebra 𝒪 A]
    {ρ₁ ρ₂ : GaloisRepAdic A} (e : ρ₁.IsEquiv ρ₂) {p : ℕ} {S : Finset ℕ}
    (h : GaloisRep.ordinaryCondition 𝒪 p S ρ₁) : GaloisRep.ordinaryCondition 𝒪 p S ρ₂ := by sorry

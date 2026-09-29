-- Prove2me | Theorems.Thm_GaloisRepAdic_flatCondition_of_isEquiv
-- name    : GaloisRepAdic.flatCondition_of_isEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/4c9fa1f0-ddc0-5969-afbf-3d1ea67fba7e
-- title:
--   Equivalence-invariance of the flat condition flatCondition 𝒪 p S
-- statement:
--   Let $A$ be a commutative local ring, let $\mathcal O$ be a commutative ring with an algebra structure $\mathcal O \to A$, and let $\rho_1,\rho_2$ be two objects of [`GaloisRepAdic A`](def/GaloisRep_Adic.html#L16), that is, free finite $A$-modules $V$ of rank $2$ together with a monoid homomorphism from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ to $\mathrm{End}_A V$ which is adically continuous (for every $n$ some finite extension of $\mathbb Q$ inside $\overline{\mathbb Q}$ has the property that elements fixing it act trivially on $V$ modulo $\mathfrak m_A^n V$). Assume $\rho_1$ and $\rho_2$ are equivalent, i.e. there is an $A$-linear isomorphism $\rho_1.V \simeq \rho_2.V$ intertwining the two Galois actions. Let $p$ be a natural number and $S$ a finite set of natural numbers, and suppose $\rho_1$ satisfies [`GaloisRep.flatCondition 𝒪 p S`](def/GaloisRep_Flat.html#L47): its determinant is cyclotomic at $p$ (that is, $p \in \mathfrak m_A$, and for all $n$, all $\sigma$ and all $a$ with $\sigma\mu = \mu^a$ on $p^n$-th roots of unity, $\det \rho_1(\sigma) \equiv a \bmod p^n$), it is flat at $p$ in the sense of [`GaloisRepAdic.IsFlatAt`](def/GaloisRep_Flat.html#L29), and it is unramified at every prime $q \notin S$. Then $\rho_2$ satisfies [`GaloisRep.flatCondition 𝒪 p S`](def/GaloisRep_Flat.html#L47) as well.
--
--   This is the elementary half of the assertion that the flat local condition at $p$ defines a deformation condition: invariance of the three constituent conditions under isomorphism of representations. It feeds into [`GaloisRep.isDeformationCondition_flatCondition`](thm.html#GaloisRep.isDeformationCondition_flatCondition), where the flat condition is packaged as a deformation condition for the modularity-lifting argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_flatCondition_of_isEquiv.lean

import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem GaloisRepAdic.flatCondition_of_isEquiv
    {A : Type} [CommRing A] [IsLocalRing A]
    (𝒪 : Type) [CommRing 𝒪] [Algebra 𝒪 A]
    {ρ₁ ρ₂ : GaloisRepAdic A} (e : ρ₁.IsEquiv ρ₂) {p : ℕ} {S : Finset ℕ}
    (h : GaloisRep.flatCondition 𝒪 p S ρ₁) : GaloisRep.flatCondition 𝒪 p S ρ₂ := by sorry

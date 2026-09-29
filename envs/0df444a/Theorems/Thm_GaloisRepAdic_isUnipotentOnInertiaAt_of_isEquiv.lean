-- Prove2me | Theorems.Thm_GaloisRepAdic_isUnipotentOnInertiaAt_of_isEquiv
-- name    : GaloisRepAdic.isUnipotentOnInertiaAt_of_isEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/0820ff3a-2262-5955-a75b-884a7fa9436f
-- title:
--   Unipotent inertia at q is invariant under equivalence
-- statement:
--   Let $A$ be a commutative local ring and let $\rho_1,\rho_2$ be two objects of [`GaloisRepAdic A`](def/GaloisRep_Adic.html#L16), that is, each consists of a free finite $A$-module $V$ of rank $2$ together with a monoid homomorphism $\rho$ from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ (the group of $\mathbb Q$-algebra automorphisms of `AlgebraicClosure ℚ`) to $\mathrm{End}_A(V)$ which is adically continuous in the sense that for every $n$ there is a finite extension $L/\mathbb Q$ inside $\overline{\mathbb Q}$ such that $\rho(\sigma)v-v \in \mathfrak m_A^n\cdot V$ for all $v \in V$ and all $\sigma$ fixing $L$ pointwise. Assume $\rho_1$ and $\rho_2$ are equivalent, i.e. there exists an $A$-linear isomorphism $\rho_1.V \to \rho_2.V$ carrying the action of each $\sigma$ through $\rho_1$ to its action through $\rho_2$. Let $q$ be a natural number, and suppose $\rho_1$ is unipotent on inertia at $q$: for every valuation subring $P$ of $\overline{\mathbb Q}$ with $q$ a nonunit of $P$, and every $\sigma$ in the image in $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ of the inertia subgroup of $P$ over $\mathbb Q$, the characteristic polynomial of $\rho_1(\sigma)$ equals $(X-1)^2$. Then the same holds for $\rho_2$. Note that $q$ is not assumed prime.
--
--   This records that the local condition of unipotent inertia at $q$ is a property of the equivalence class of a two-dimensional adic Galois representation, as is needed for such conditions to cut out subfunctors of Mazur's deformation functor. It is used in the analysis of the Galois representations attached to Hecke rings at Taylor–Wiles levels, and is repackaged as [`GaloisRepAdic.IsEquiv.isUnipotentOnInertiaAt`](thm.html#GaloisRepAdic.IsEquiv.isUnipotentOnInertiaAt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_isUnipotentOnInertiaAt_of_isEquiv.lean

import Definitions.Def_GaloisRep_LocalConditions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem GaloisRepAdic.isUnipotentOnInertiaAt_of_isEquiv
    {A : Type} [CommRing A] [IsLocalRing A]
    {ρ₁ ρ₂ : GaloisRepAdic A} (e : ρ₁.IsEquiv ρ₂) {q : ℕ}
    (h : ρ₁.IsUnipotentOnInertiaAt q) : ρ₂.IsUnipotentOnInertiaAt q := by sorry

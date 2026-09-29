-- Prove2me | Theorems.Thm_GaloisRepAdic_isUnipotentOnInertiaAt_baseChangeAlong
-- name    : GaloisRepAdic.isUnipotentOnInertiaAt_baseChangeAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/286e1819-ebac-54ea-a7c6-7fc8e41d9c87
-- title:
--   Unipotent inertia at q survives base change
-- statement:
--   Let $A$ and $B$ be commutative local rings and let $\varphi\colon A\to B$ be a ring homomorphism which is local (non-units are sent to non-units). Let $\rho$ be an element of [`GaloisRepAdic A`](def/GaloisRep_Adic.html#L16), that is, a free finite $A$-module $V$ of rank $2$ together with a monoid homomorphism from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ to $\mathrm{End}_A(V)$ that is adically continuous in the sense that for each $n$ there is a finite extension $L/\mathbb Q$ inside $\overline{\mathbb Q}$ with $\rho(\sigma)v-v\in(\mathfrak m_A^n)\cdot V$ for all $v\in V$ and all $\sigma$ fixing $L$ pointwise. Fix a natural number $q$, and assume $\rho$ satisfies `IsUnipotentOnInertiaAt q`: for every valuation subring $P$ of $\overline{\mathbb Q}$ with $q$ a non-unit of $P$, and every $\sigma$ in the image in $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ of the inertia subgroup of $P$ over $\mathbb Q$, the characteristic polynomial of $\rho(\sigma)$ equals $(X-1)^2$. The conclusion is that the base change $\rho.\mathrm{baseChangeAlong}\ \varphi$, with module $B\otimes_A V$ and operators $\rho(\sigma)\otimes_A\mathrm{id}$, again satisfies `IsUnipotentOnInertiaAt q`.
--
--   This records that the local condition of unipotent inertia at $q$ is stable under extension of the coefficient ring along a local homomorphism, as is needed for it to cut out a subfunctor of the deformation functor. It is used wherever deformations subject to this condition are transported to a quotient ring or to a Hecke algebra, and in the level-lowering and modularity-lifting arguments that invoke such deformation data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_isUnipotentOnInertiaAt_baseChangeAlong.lean

import Definitions.Def_GaloisRep_LocalConditions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem GaloisRepAdic.isUnipotentOnInertiaAt_baseChangeAlong
    {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (φ : A →+* B) (hφ : IsLocalHom φ)
    (ρ : GaloisRepAdic A) {q : ℕ} (h : ρ.IsUnipotentOnInertiaAt q) :
    (ρ.baseChangeAlong φ hφ).IsUnipotentOnInertiaAt q := by sorry

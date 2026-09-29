-- Prove2me | Theorems.Thm_GaloisRepAdic_isUnipotentOnInertiaAt_of_isUnramifiedAt
-- name    : GaloisRepAdic.isUnipotentOnInertiaAt_of_isUnramifiedAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/03c271ff-a847-5b90-ade9-8d4fb0b196de
-- title:
--   Unramified at q implies unipotent on inertia at q
-- statement:
--   Let $A$ be a commutative local ring and let $\rho$ be an adic Galois representation over $A$ in the sense of [`GaloisRepAdic`](def/GaloisRep_Adic.html#L16): a module $V$ over $A$ that is free and finite with $\operatorname{finrank}_A V = 2$, together with a monoid homomorphism from $\operatorname{Gal}(\overline{\mathbb Q}/\mathbb Q)$ (realised as the $\mathbb Q$-algebra automorphisms of $\mathrm{AlgebraicClosure}\ \mathbb Q$) to $\operatorname{End}_A V$, subject to the adic continuity condition that for every $n$ there is a finite extension $L/\mathbb Q$ inside $\overline{\mathbb Q}$ such that every $\sigma$ fixing $L$ pointwise satisfies $\rho(\sigma)v - v \in \mathfrak m_A^n \cdot V$ for all $v \in V$. Let $q$ be a natural number, and assume $\rho$ is unramified at $q$, meaning: for every valuation subring $P$ of $\overline{\mathbb Q}$ with $q$ a nonunit of $P$, and every $\sigma$ in the image in $\operatorname{Gal}(\overline{\mathbb Q}/\mathbb Q)$ of the inertia subgroup of $P$ over $\mathbb Q$, one has $\rho(\sigma) = 1$. The conclusion is that $\rho$ is unipotent on inertia at $q$: for every such $P$ and every such inertia element $\sigma$, the characteristic polynomial of the $A$-linear endomorphism $\rho(\sigma)$ equals $(X-1)^2$.
--
--   This is the elementary compatibility between the two local conditions at a prime $q$ used in the library: triviality of the inertia action is a special case of the unipotence condition imposed on inertia. It lets primes of good reduction, where the Tate module is unramified, be fed into the same unipotence hypothesis as primes of multiplicative reduction in the level-stripping step of the modularity-lifting assembly, and it is used by several results on Hecke-algebra Galois representations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_isUnipotentOnInertiaAt_of_isUnramifiedAt.lean

import Definitions.Def_GaloisRep_LocalConditions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem GaloisRepAdic.isUnipotentOnInertiaAt_of_isUnramifiedAt {A : Type} [CommRing A] [IsLocalRing A]
    (ρ : GaloisRepAdic A) {q : ℕ} (h : ρ.IsUnramifiedAt q) : ρ.IsUnipotentOnInertiaAt q := by sorry

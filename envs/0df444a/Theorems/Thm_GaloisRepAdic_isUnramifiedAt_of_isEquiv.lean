-- Prove2me | Theorems.Thm_GaloisRepAdic_isUnramifiedAt_of_isEquiv
-- name    : GaloisRepAdic.isUnramifiedAt_of_isEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/337e3d3a-54a1-5987-8ad4-c2675cd70d0f
-- title:
--   Unramifiedness at q is invariant under equivalence
-- statement:
--   Let $A$ be a commutative local ring and let $\rho_1,\rho_2$ be two adic Galois representations over $A$ in the sense of [`GaloisRepAdic`](def/GaloisRep_Adic.html#L16): each consists of an $A$-module $V$ that is free and finite with $\operatorname{rank}_A V = 2$, a monoid homomorphism $\rho$ from the group of $\mathbb{Q}$-algebra automorphisms of $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ to $\operatorname{End}_A V$, and the adic continuity condition that for every $n$ there is a finite extension $L/\mathbb{Q}$ inside $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ such that every automorphism fixing $L$ pointwise satisfies $\rho(\sigma)v - v \in (\mathfrak{m}_A^n) \cdot V$ for all $v \in V$. Assume $\rho_1$ and $\rho_2$ are equivalent, i.e. there exists an $A$-linear isomorphism $\rho_1.V \to \rho_2.V$ with $f(\rho_1(\sigma)x) = \rho_2(\sigma)(f(x))$ for all $\sigma$ and all $x$. Let $q$ be a natural number (no primality is assumed) and suppose $\rho_1$ is unramified at $q$, meaning: for every valuation subring $P$ of $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ with $q$ a nonunit of $P$, and every $\sigma$ in the image in $\mathrm{Gal}(\mathrm{AlgebraicClosure}\ \mathbb{Q}/\mathbb{Q})$ of the inertia subgroup of $P$ over $\mathbb{Q}$, one has $\rho_1(\sigma) = 1$. Then $\rho_2$ is unramified at $q$ in the same sense.
--
--   This records that the local condition of being unramified at $q$ is a property of the equivalence class of a representation, as is required for unramifiedness conditions to cut out subfunctors of the deformation functor. It is used in the treatment of the ordinary and minimal deformation conditions and in the Hecke-algebra patching arguments, for instance by [`CuspForm.HeckeGaloisRepDatum.isUnramifiedAt_of_notMem`](thm.html#CuspForm.HeckeGaloisRepDatum.isUnramifiedAt_of_notMem).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_isUnramifiedAt_of_isEquiv.lean

import Definitions.Def_GaloisRep_LocalConditions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem GaloisRepAdic.isUnramifiedAt_of_isEquiv
    {A : Type} [CommRing A] [IsLocalRing A]
    {ρ₁ ρ₂ : GaloisRepAdic A} (e : ρ₁.IsEquiv ρ₂) {q : ℕ}
    (h : ρ₁.IsUnramifiedAt q) : ρ₂.IsUnramifiedAt q := by sorry

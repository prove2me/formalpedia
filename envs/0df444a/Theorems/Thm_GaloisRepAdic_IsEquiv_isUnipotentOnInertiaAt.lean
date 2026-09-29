-- Prove2me | Theorems.Thm_GaloisRepAdic_IsEquiv_isUnipotentOnInertiaAt
-- name    : GaloisRepAdic.IsEquiv.isUnipotentOnInertiaAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/d03573ad-81bb-5d46-83ad-9ff2d4a9cbc2
-- title:
--   Unipotence on inertia at q is invariant under equivalence
-- statement:
--   Let $\mathcal{O}$ be a commutative ring, let $A$ be a commutative local ring equipped with an $\mathcal{O}$-algebra structure, and let $q$ be a natural number. Let $\rho$ and $\rho'$ be two-dimensional adic Galois representations over $A$ in the sense of the project: each consists of a free finite $A$-module $V$ with $\operatorname{rank}_A V = 2$, a monoid homomorphism from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ (realised as the $\mathbb{Q}$-algebra automorphisms of $\mathrm{AlgebraicClosure}\ \mathbb{Q}$) to $\operatorname{End}_A V$, and the continuity condition that for every $n$ there is a finite extension $L/\mathbb{Q}$ inside $\overline{\mathbb{Q}}$ such that every automorphism fixing $L$ pointwise acts trivially on $V$ modulo $\mathfrak{m}_A^n V$. Assume $\rho$ and $\rho'$ are equivalent, i.e. there exists an $A$-linear isomorphism of their underlying modules intertwining the two actions of every $\sigma$. Then if $\rho$ is unipotent on inertia at $q$ — meaning that for every valuation subring $P$ of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $P$, and every $\sigma$ in the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $P$ over $\mathbb{Q}$, the characteristic polynomial of $\rho(\sigma)$ is $(X-1)^2$ — the same holds for $\rho'$.
--
--   This records the invariance under isomorphism of the local condition of unipotent (Steinberg-type) behaviour of inertia at $q$, the condition being an identity of characteristic polynomials and hence stable under conjugation. It is used in the construction of patching data and in the local analysis of Hecke algebras at level-raising primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_IsEquiv_isUnipotentOnInertiaAt.lean

import Definitions.Def_GaloisRep_DeformationRingData
import Definitions.Def_CuspForm_HeckeGaloisRepDatum
import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_CuspForm_IntegralStructure
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_GaloisRep_ResidualEquiv
import Definitions.Def_Algebra_PatchingDatum
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Length

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem GaloisRepAdic.IsEquiv.isUnipotentOnInertiaAt
    {𝒪 : Type} [CommRing 𝒪] {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A]
    (q : ℕ) (ρ ρ' : GaloisRepAdic A) (h : ρ.IsEquiv ρ') :
    ρ.IsUnipotentOnInertiaAt q → ρ'.IsUnipotentOnInertiaAt q := by sorry

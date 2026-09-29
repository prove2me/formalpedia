-- Prove2me | Theorems.Thm_Module_FaithfullyFlat_exists_ringHom_comp_algebraMap_eq_of_finiteType_of_isAlgClosed
-- name    : Module.FaithfullyFlat.exists_ringHom_comp_algebraMap_eq_of_finiteType_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/178d6fd5-16f8-5dc8-b44a-6950c8d67bb5
-- title:
--   Lifting geometric points along a faithfully flat finite-type algebra
-- statement:
--   Let $S$ and $S'$ be commutative rings in a common universe, with $S'$ an $S$-algebra which is faithfully flat as an $S$-module and of finite type as an $S$-algebra, and let $k$ be an algebraically closed field. The assertion is that for every ring homomorphism $sk : S \to k$ there exists a ring homomorphism $\sigma : S' \to k$ whose composite with the structure map $\mathrm{algebraMap}\ S\ S' : S \to S'$ equals $sk$; that is, every geometric point of $\operatorname{Spec} S$ with values in $k$ lifts to a $k$-valued point of $\operatorname{Spec} S'$. The equality asserted is an equality of ring homomorphisms $S \to k$, not merely a pointwise statement about a chosen element, and no compatibility beyond that equality is claimed; in particular the lift $\sigma$ is not asserted to be unique.
--
--   This is the Nullstellensatz-type surjectivity on $k$-points of a faithfully flat finite-type cover: $\operatorname{Spec} S' \to \operatorname{Spec} S$ hits every $k$-valued point when $k$ is algebraically closed. It is used to produce points of fppf-type covers in the treatment of polarised abelian schemes, being cited by [`AlgebraicGeometry.Polarisation.exists_isInvertible_nonempty_iso_tensor_pullback_negMor_geomFibre_of_field`](thm.html#AlgebraicGeometry.Polarisation.exists_isInvertible_nonempty_iso_tensor_pullback_negMor_geomFibre_of_field) and [`AlgebraicGeometry.PolarisedAbelianScheme.exists_eq_comp_of_memKernel_of_isOfType_of_isAlgClosed`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.exists_eq_comp_of_memKernel_of_isOfType_of_isAlgClosed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_FaithfullyFlat_exists_ringHom_comp_algebraMap_eq_of_finiteType_of_isAlgClosed.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem Module.FaithfullyFlat.exists_ringHom_comp_algebraMap_eq_of_finiteType_of_isAlgClosed
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S']
    [Module.FaithfullyFlat S S'] [Algebra.FiniteType S S']
    (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k) :
    ∃ σ : S' →+* k, σ.comp (algebraMap S S') = sk := by sorry

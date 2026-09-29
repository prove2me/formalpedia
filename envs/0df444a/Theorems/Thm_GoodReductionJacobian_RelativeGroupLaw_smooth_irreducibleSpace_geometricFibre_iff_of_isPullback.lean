-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_smooth_irreducibleSpace_geometricFibre_iff_of_isPullback
-- name    : GoodReductionJacobian.RelativeGroupLaw.smooth_irreducibleSpace_geometricFibre_iff_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/8ef6d350-fd34-5eb1-b491-d70447233d4d
-- title:
--   Fibre smoothness, irreducibility, dimension and group law along a cartesian square
-- statement:
--   Let $\psi : R \to R'$ be a homomorphism of commutative rings, let $Z, Z'$ be schemes, and let $f : Z \to \operatorname{Spec} R$, $f' : Z' \to \operatorname{Spec} R'$ and $g_Z : Z' \to Z$ be morphisms such that the square with sides $g_Z$, $f'$, $f$ and $\operatorname{Spec}(\psi)$ is cartesian. Let $g$ be a natural number, $k$ a commutative ring and $x' : R' \to k$ a ring homomorphism. The assertion is an equivalence of two conjunctions of four statements. On one side, for the base change $P' := Z' \times_{\operatorname{Spec} R'} \operatorname{Spec} k$ formed along $\operatorname{Spec}(x')$: its second projection $P' \to \operatorname{Spec} k$ is smooth, the underlying topological space of $P'$ is an irreducible space, its topological Krull dimension equals $g$, and the type of `RelativeGroupLaw` structures on that projection is nonempty, i.e. there exist functorial operations assigning to each $t : T \to \operatorname{Spec} k$ a multiplication, a unit and an inverse on the set of morphisms $\varphi : T \to P'$ with $\varphi$ followed by the projection equal to $t$, satisfying associativity, both unit laws and left inversion, with the multiplication natural in $T$ under precomposition with morphisms compatible with the structure maps. On the other side, the same four statements for the base change of $f$ along $\operatorname{Spec}(x' \circ \psi)$ and its second projection.
--
--   This is the invariance of the geometric-fibre conditions defining an abelian scheme (smooth, irreducible, of relative dimension $g$, carrying a group law) under a base change of the base ring: the fibre of $f'$ over a point $x'$ of $\operatorname{Spec} R'$ agrees with the fibre of $f$ over its image $x' \circ \psi$. It is used in the study of the locus in the base over which the geometric fibres are abelian varieties, namely by [`GoodReductionJacobian.AbelianSchemePropertyBundle.isOpen_setOf_abelian_geometricFibre_and_preimage_eq_of_isPullback`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.isOpen_setOf_abelian_geometricFibre_and_preimage_eq_of_isPullback) and [`GoodReductionJacobian.AbelianSchemePropertyBundle.isOpen_setOf_not_mem_and_abelian_geometricFibre`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.isOpen_setOf_not_mem_and_abelian_geometricFibre).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_smooth_irreducibleSpace_geometricFibre_iff_of_isPullback.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
attribute [local instance] MvPolynomial.gradedAlgebra

theorem GoodReductionJacobian.RelativeGroupLaw.smooth_irreducibleSpace_geometricFibre_iff_of_isPullback
    {R R' : Type} [CommRing R] [CommRing R'] (ψ : R →+* R')
    {Z Z' : Scheme.{0}} (f : Z ⟶ Spec (CommRingCat.of R)) (f' : Z' ⟶ Spec (CommRingCat.of R'))
    (gZ : Z' ⟶ Z) (hpb : IsPullback gZ f' f (Spec.map (CommRingCat.ofHom ψ)))
    (g : ℕ) (k : Type) [CommRing k] (x' : R' →+* k) :
    (Smooth (pullback.snd f' (Spec.map (CommRingCat.ofHom x'))) ∧
        IrreducibleSpace ↥(pullback f' (Spec.map (CommRingCat.ofHom x'))) ∧
        topologicalKrullDim ↥(pullback f' (Spec.map (CommRingCat.ofHom x'))) = g ∧
        Nonempty (RelativeGroupLaw k (pullback.snd f' (Spec.map (CommRingCat.ofHom x'))))) ↔
    (Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom (x'.comp ψ)))) ∧
        IrreducibleSpace ↥(pullback f (Spec.map (CommRingCat.ofHom (x'.comp ψ)))) ∧
        topologicalKrullDim ↥(pullback f (Spec.map (CommRingCat.ofHom (x'.comp ψ)))) = g ∧
        Nonempty (RelativeGroupLaw k (pullback.snd f (Spec.map (CommRingCat.ofHom (x'.comp ψ)))))) := by sorry

-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_smooth_irreducibleSpace_geometricFibre_iff_of_ker_eq_ker
-- name    : GoodReductionJacobian.RelativeGroupLaw.smooth_irreducibleSpace_geometricFibre_iff_of_ker_eq_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/4cc70e2e-ed8d-546d-83b0-4be2b81af9de
-- title:
--   Independence of the geometric point for abelian fibre conditions
-- statement:
--   Let $R$ be a commutative ring and let $f : Z \to \operatorname{Spec} R$ be a morphism of schemes that is proper, flat and locally of finite presentation, and assume $f$ admits a projective factorisation: for some $N$ there is a closed immersion $\iota : Z \to \operatorname{Proj}$ of the homogeneous-submodule graded algebra of $R[x_0,\dots,x_N]$ such that $\iota$ followed by the structure morphism $\mathbb{P}^N_R \to \operatorname{Spec} R$ equals $f$. Assume also given a section $\varepsilon$ of $f$ over the identity of $\operatorname{Spec} R$, that is a morphism $\operatorname{Spec} R \to Z$ whose composite with $f$ is the identity, a natural number $g$, and two ring homomorphisms $x_1 : R \to k_1$, $x_2 : R \to k_2$ into algebraically closed fields with $\ker x_1 = \ker x_2$ (two geometric points lying over the same point of $\operatorname{Spec} R$). Then the following four conditions hold for the base change $Z \times_{\operatorname{Spec} R} \operatorname{Spec} k_1 \to \operatorname{Spec} k_1$ if and only if they hold for the base change along $x_2$: the projection to $\operatorname{Spec} k_i$ is smooth; the underlying topological space of the fibre product is irreducible; its topological Krull dimension equals $g$; and there exists a `RelativeGroupLaw` over $k_i$ for that projection, i.e. an assignment, to every $k_i$-scheme $t : T \to \operatorname{Spec} k_i$, of a multiplication, a unit and an inversion on the set of morphisms $T \to Z \times_{\operatorname{Spec} R}\operatorname{Spec} k_i$ lying over $t$, satisfying associativity, the two unit laws and the left inverse law, with multiplication compatible with precomposition by any $\psi : T' \to T$ over $\operatorname{Spec} k_i$.
--
--   This is the statement that the conditions defining an abelian variety fibre — smoothness, geometric irreducibility, dimension $g$, and the presence of a functorial group law — depend only on the point of $\operatorname{Spec} R$ underlying a geometric point, not on the chosen algebraically closed field. It feeds the proof that the locus of points of the base whose geometric fibre is an abelian variety of dimension $g$ is open, in the treatment of good reduction of Jacobians.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_smooth_irreducibleSpace_geometricFibre_iff_of_ker_eq_ker.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open GoodReductionJacobian
attribute [local instance] MvPolynomial.gradedAlgebra

theorem GoodReductionJacobian.RelativeGroupLaw.smooth_irreducibleSpace_geometricFibre_iff_of_ker_eq_ker
    {R : Type} [CommRing R] {Z : Scheme.{0}} (f : Z ⟶ Spec (CommRingCat.of R))
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (hproj : ∃ (N : ℕ) (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)),
      IsClosedImmersion ι ∧ ι ≫ ProjSpace.π R N = f)
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) (g : ℕ)
    (k₁ : Type) [Field k₁] [IsAlgClosed k₁] (x₁ : R →+* k₁)
    (k₂ : Type) [Field k₂] [IsAlgClosed k₂] (x₂ : R →+* k₂)
    (hker : RingHom.ker x₁ = RingHom.ker x₂) :
    (Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom x₁))) ∧
        IrreducibleSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x₁))) ∧
        topologicalKrullDim ↥(pullback f (Spec.map (CommRingCat.ofHom x₁))) = g ∧
        Nonempty (RelativeGroupLaw k₁ (pullback.snd f (Spec.map (CommRingCat.ofHom x₁))))) ↔
    (Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom x₂))) ∧
        IrreducibleSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x₂))) ∧
        topologicalKrullDim ↥(pullback f (Spec.map (CommRingCat.ofHom x₂))) = g ∧
        Nonempty (RelativeGroupLaw k₂ (pullback.snd f (Spec.map (CommRingCat.ofHom x₂))))) := by sorry

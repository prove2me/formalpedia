-- Prove2me | Theorems.Thm_GoodReductionJacobian_exists_relativeGroupLaw_one_eq_and_isCommutative_of_forall_abelian_geometricFibre
-- name    : GoodReductionJacobian.exists_relativeGroupLaw_one_eq_and_isCommutative_of_forall_abelian_geometricFibre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/4170394c-da10-5640-a5ad-9fc1b4f1d568
-- title:
--   Unique commutative relative group law from abelian geometric fibres
-- statement:
--   Let $R$ be a commutative ring, $Z$ a scheme and $f : Z \to \operatorname{Spec} R$ a morphism that is proper, flat and locally of finite presentation. Assume `hproj`: for some $N$ there is a closed immersion $\iota$ of $Z$ into $\operatorname{Proj}$ of the graded ring of homogeneous components of $R[x_0,\dots,x_N]$ (projective $N$-space over $R$) such that $\iota$ followed by the structure morphism `ProjSpace.π R N` equals $f$. Let $g$ be a natural number and let $\varepsilon$ be an element of `SchemeHomOver (𝟙 _) f`, i.e. a morphism $\operatorname{Spec} R \to Z$ composing with $f$ to the identity (a section). Assume `hab`: for every point $s$ of $\operatorname{Spec} R$, every algebraically closed field $k$ and every ring homomorphism $x : R \to k$ with kernel the prime of $s$, the projection $Z \times_{\operatorname{Spec} R} \operatorname{Spec} k \to \operatorname{Spec} k$ is smooth, the fibre product is an irreducible space of topological Krull dimension $g$, and the type `RelativeGroupLaw k` of relative group laws on that projection is nonempty. The conclusion asserts the existence of a relative group law $L$ on $f$ over $R$ — that is, for each $T \to \operatorname{Spec} R$ a multiplication, unit and inverse on the set of $T$-points of $Z$ over $\operatorname{Spec} R$, satisfying associativity, both unit laws, left inverses, and naturality of the multiplication under precomposition with morphisms $T' \to T$ over $\operatorname{Spec} R$ — such that the unit of $L$ at the identity of $\operatorname{Spec} R$ is $\varepsilon$, $L$ is commutative (the multiplications on all $T$-point sets commute), and every relative group law on $f$ whose unit at the identity is $\varepsilon$ equals $L$.
--
--   This is the statement that a projective, flat, finitely presented family with a section all of whose geometric fibres are smooth irreducible $g$-dimensional schemes carrying a group law is an abelian scheme in the functorial sense, with its group law uniquely determined by the section; the Noetherian hypothesis on the base is removed here. It feeds the construction of the moduli-theoretic representability statement [`AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_isImmersion_proj_represents_embedded_of_isNoetherianRing`](thm.html#AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_isImmersion_proj_represents_embedded_of_isNoetherianRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_exists_relativeGroupLaw_one_eq_and_isCommutative_of_forall_abelian_geometricFibre.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits NeronModelInfra
open AlgebraicGeometry
open GoodReductionJacobian
attribute [local instance] MvPolynomial.gradedAlgebra

theorem GoodReductionJacobian.exists_relativeGroupLaw_one_eq_and_isCommutative_of_forall_abelian_geometricFibre
    {R : Type} [CommRing R] {Z : Scheme.{0}} (f : Z ⟶ Spec (CommRingCat.of R))
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (hproj : ∃ (N : ℕ) (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)),
      IsClosedImmersion ι ∧ ι ≫ ProjSpace.π R N = f)
    (g : ℕ) (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    (hab : ∀ (s : ↥(Spec (CommRingCat.of R))) (k : Type) [Field k] [IsAlgClosed k] (x : R →+* k),
        RingHom.ker x = s.asIdeal →
        Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom x))) ∧
        IrreducibleSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x))) ∧
        topologicalKrullDim ↥(pullback f (Spec.map (CommRingCat.ofHom x))) = g ∧
        Nonempty (RelativeGroupLaw k (pullback.snd f (Spec.map (CommRingCat.ofHom x))))) :
    ∃ L : RelativeGroupLaw R f, L.one (𝟙 _) = ε ∧ L.IsCommutative ∧
      ∀ L' : RelativeGroupLaw R f, L'.one (𝟙 _) = ε → L' = L := by sorry

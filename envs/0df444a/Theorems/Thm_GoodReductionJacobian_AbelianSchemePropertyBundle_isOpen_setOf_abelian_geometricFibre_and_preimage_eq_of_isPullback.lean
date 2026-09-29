-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_isOpen_setOf_abelian_geometricFibre_and_preimage_eq_of_isPullback
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.isOpen_setOf_abelian_geometricFibre_and_preimage_eq_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/8f34a84b-7bb8-546d-b82c-4f1ad7f81ef8
-- title:
--   Openness and base change of the abelian-fibre locus
-- statement:
--   Let $R$ be a commutative ring, $Z$ a scheme, and $f : Z \to \operatorname{Spec} R$ a proper, flat morphism that is locally of finite presentation; assume moreover that there are an $N \in \mathbb{N}$ and a closed immersion $\iota : Z \to \operatorname{Proj}$ of the graded ring of homogeneous polynomials in $N+1$ variables over $R$ with $\iota$ followed by the structure map $\mathtt{ProjSpace.}\pi\ R\ N$ equal to $f$, let $g \in \mathbb{N}$, and let $\varepsilon$ be a section of $f$, i.e. a morphism $\operatorname{Spec} R \to Z$ whose composite with $f$ is the identity. For a morphism $h : W \to \operatorname{Spec} A$ write $P_g(h)$ for the set of points $s$ of $\operatorname{Spec} A$ such that for every algebraically closed field $k$ and every ring homomorphism $x : A \to k$ with $\ker x$ equal to the prime ideal of $s$, the projection of $W \times_{\operatorname{Spec} A} \operatorname{Spec} k$ to $\operatorname{Spec} k$ is smooth, the pullback scheme is an irreducible topological space of topological Krull dimension $g$, and there exists a `RelativeGroupLaw` on it over $k$, that is, a functorial assignment to each $k$-scheme $T$ of a group structure on the set of $T$-points, given by multiplication, unit and inverse operations satisfying associativity, the two unit laws and left inversion, with multiplication compatible with pullback along morphisms of $k$-schemes. The conclusion is twofold: $P_g(f)$ is open in $\operatorname{Spec} R$; and for every commutative ring $R'$, ring homomorphism $\psi : R \to R'$, scheme $Z'$, morphism $f' : Z' \to \operatorname{Spec} R'$ and morphism $gZ : Z' \to Z$ making the square with $f'$, $f$ and $\operatorname{Spec}\psi$ cartesian, one has $P_g(f') = (\operatorname{Spec}\psi)^{-1}\bigl(P_g(f)\bigr)$ as subsets of the underlying spaces.
--
--   This is the openness and base-change compatibility of the locus in the base over which a flat projective family with a section has abelian-variety fibres of dimension $g$ — the geometric input needed to descend a fibrewise group law to an abelian scheme structure. It is used in the construction of relative group laws on Jacobians of good-reduction curves and in the embedding of framed polarised abelian schemes into projective space over a Noetherian base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_isOpen_setOf_abelian_geometricFibre_and_preimage_eq_of_isPullback.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.isOpen_setOf_abelian_geometricFibre_and_preimage_eq_of_isPullback
    {R : Type} [CommRing R] {Z : Scheme.{0}} (f : Z ⟶ Spec (CommRingCat.of R))
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (hproj : ∃ (N : ℕ) (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)),
      IsClosedImmersion ι ∧ ι ≫ ProjSpace.π R N = f)
    (g : ℕ) (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    IsOpen {s : ↥(Spec (CommRingCat.of R)) | ∀ (k : Type) [Field k] [IsAlgClosed k] (x : R →+* k),
        RingHom.ker x = s.asIdeal →
        Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom x))) ∧
        IrreducibleSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x))) ∧
        topologicalKrullDim ↥(pullback f (Spec.map (CommRingCat.ofHom x))) = g ∧
        Nonempty (RelativeGroupLaw k (pullback.snd f (Spec.map (CommRingCat.ofHom x))))} ∧
    ∀ (R' : Type) [CommRing R'] (ψ : R →+* R') (Z' : Scheme.{0}) (f' : Z' ⟶ Spec (CommRingCat.of R'))
      (gZ : Z' ⟶ Z) (_hpb : IsPullback gZ f' f (Spec.map (CommRingCat.ofHom ψ))),
      {s : ↥(Spec (CommRingCat.of R')) | ∀ (k : Type) [Field k] [IsAlgClosed k] (x : R' →+* k),
          RingHom.ker x = s.asIdeal →
          Smooth (pullback.snd f' (Spec.map (CommRingCat.ofHom x))) ∧
          IrreducibleSpace ↥(pullback f' (Spec.map (CommRingCat.ofHom x))) ∧
          topologicalKrullDim ↥(pullback f' (Spec.map (CommRingCat.ofHom x))) = g ∧
          Nonempty (RelativeGroupLaw k (pullback.snd f' (Spec.map (CommRingCat.ofHom x))))} =
        (Spec.map (CommRingCat.ofHom ψ)).base ⁻¹' {s : ↥(Spec (CommRingCat.of R)) | ∀ (k : Type) [Field k] [IsAlgClosed k] (x : R →+* k),
            RingHom.ker x = s.asIdeal →
            Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom x))) ∧
            IrreducibleSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x))) ∧
            topologicalKrullDim ↥(pullback f (Spec.map (CommRingCat.ofHom x))) = g ∧
            Nonempty (RelativeGroupLaw k (pullback.snd f (Spec.map (CommRingCat.ofHom x))))} := by sorry

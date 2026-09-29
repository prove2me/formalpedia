-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_isClosedImmersion_lfp_forall_iff_locIsoOnBase_pullback
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_isClosedImmersion_lfp_forall_iff_locIsoOnBase_pullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/14061126-2613-50a0-ba85-1cb27d108c0a
-- title:
--   Picard equality locus on an abelian scheme is closed
-- statement:
--   Let $S$ be a commutative ring, let $A$ be a scheme and $f : A \to \operatorname{Spec} S$ a morphism, let $L$ be a relative group law on $f$ (a group structure on the sections $\{\varphi : T \to A \mid \varphi \circ f = t\}$ over every $t : T \to \operatorname{Spec} S$, with unit, inverse, associativity and compatibility with base change along $T' \to T$), and let `hA` assert that $f$ is smooth and proper, has connected fibres over every point of $\operatorname{Spec} S$, and admits a relative group law. Let $\mathcal M, \mathcal N$ be modules on $A$, each invertible in the sense that every point of $A$ has an open neighbourhood $U$ on which the restriction is isomorphic to the unit module of $U$. The assertion is that there exist a scheme $Z$ and a morphism $\iota : Z \to \operatorname{Spec} S$ which is a closed immersion and locally of finite presentation, such that for every commutative ring $S'$, every ring homomorphism $\varphi : S \to S'$, and every $f' : A' \to \operatorname{Spec} S'$ together with $g : A' \to A$ making the square formed by $g$, $f'$, $f$ and $\operatorname{Spec} \varphi$ cartesian, the morphism $\operatorname{Spec} \varphi$ factors through $\iota$ (i.e. there is $y : \operatorname{Spec} S' \to Z$ with $y$ followed by $\iota$ equal to $\operatorname{Spec} \varphi$) if and only if $g^{*}\mathcal M$ and $g^{*}\mathcal N$ are isomorphic locally on the base, that is, every point $s$ of $\operatorname{Spec} S'$ has an open neighbourhood $U$ with $g^{*}\mathcal M$ and $g^{*}\mathcal N$ isomorphic after restriction to $f'^{-1}(U)$.
--
--   This is the representability, by a closed subscheme of the base whose immersion is locally of finite presentation, of the locus over which two invertible sheaves on an abelian scheme become isomorphic locally on the base; it is the seesaw-type input used to cut out closed loci defined by coincidence of polarisation data. It is cited in the construction of the closed locus attached to a polarised abelian scheme and in the statement producing an ideal of $S$ governing Rosati compatibility under base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_isClosedImmersion_lfp_forall_iff_locIsoOnBase_pullback.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_isClosedImmersion_lfp_forall_iff_locIsoOnBase_pullback
    {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f)
    (𝓜 𝓝 : A.Modules) (h𝓜 : Scheme.Modules.IsInvertible 𝓜) (h𝓝 : Scheme.Modules.IsInvertible 𝓝) :
    ∃ (Z : Scheme.{0}) (ι : Z ⟶ Spec (CommRingCat.of S)), IsClosedImmersion ι ∧ LocallyOfFinitePresentation ι ∧
      ∀ (S' : Type) [CommRing S'] (φ : S →+* S') {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of S')} (g : A' ⟶ A),
        IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)) →
        ((∃ y : Spec (CommRingCat.of S') ⟶ Z, y ≫ ι = Spec.map (CommRingCat.ofHom φ)) ↔
          LocIsoOnBase f' ((Scheme.Modules.pullback g).obj 𝓜) ((Scheme.Modules.pullback g).obj 𝓝)) := by sorry

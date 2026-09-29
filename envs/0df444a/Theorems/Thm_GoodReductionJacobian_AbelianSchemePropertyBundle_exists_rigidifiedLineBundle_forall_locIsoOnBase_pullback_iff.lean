-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_rigidifiedLineBundle_forall_locIsoOnBase_pullback_iff
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_rigidifiedLineBundle_forall_locIsoOnBase_pullback_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/a42f41a5-8564-54ad-8a04-e7c4e457885c
-- title:
--   A rigidified bundle detecting local isomorphy on the base
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} S$ a morphism, equipped with a relative group law $L$ on $f$ (functorial multiplication, unit and inverse on $T$-points over $\operatorname{Spec} S$, satisfying the group axioms and compatible with base change in $T$), and assume `AbelianSchemePropertyBundle S f`, i.e. $f$ is smooth and proper, each fibre $f^{-1}(s)$ is connected, and $f$ admits a relative group law. Let $\mathcal M,\mathcal N$ be $\mathcal O_A$-modules, each invertible in the sense that every point of $A$ has an open neighbourhood $U$ with $\mathcal M|_U$ (resp. $\mathcal N|_U$) isomorphic to the structure sheaf of $U$. The assertion is that there exists a line bundle $M$ on the fibre product of $f$ with the identity of $\operatorname{Spec} S$, invertible and rigidified along the unit section $L.\mathrm{one}$ of $L$, with the following property, uniformly in all base changes: for every commutative ring $S'$, every ring homomorphism $\varphi : S \to S'$, every scheme $A'$ with $f' : A' \to \operatorname{Spec} S'$ and every $g : A' \to A$ such that the square formed by $g$, $f'$, $f$ and $\operatorname{Spec} \varphi$ is cartesian, the following are equivalent: (i) $g^*\mathcal M$ and $g^*\mathcal N$ are locally isomorphic on the base, i.e. every point $s \in \operatorname{Spec} S'$ has an open neighbourhood $U$ such that the restrictions of $g^*\mathcal M$ and $g^*\mathcal N$ to $f'^{-1}(U)$ are isomorphic; (ii) the underlying module of the base change of $M$ along $\operatorname{Spec} \varphi$, viewed as a morphism over the identity of $\operatorname{Spec} S$, is isomorphic to the underlying module of the trivial rigidified bundle over $\operatorname{Spec} \varphi$. Note that (ii) requires only an isomorphism of modules, not one compatible with the rigidifications.
--
--   This is the "rigidified difference" construction attached to a pair of invertible sheaves on an abelian scheme, classically $\mathcal M \otimes \mathcal N^{\vee}$ normalised along the unit section, together with the seesaw-type criterion that its triviality after base change detects local isomorphy on the base. It is used to compare a cartesian square presented by a consumer with a fixed base change, and feeds into the description of the locus where two invertible sheaves become isomorphic locally on the base as a closed, locally finitely presented subfunctor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_rigidifiedLineBundle_forall_locIsoOnBase_pullback_iff.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_rigidifiedLineBundle_forall_locIsoOnBase_pullback_iff
    {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f)
    (𝓜 𝓝 : A.Modules) (h𝓜 : Scheme.Modules.IsInvertible 𝓜) (h𝓝 : Scheme.Modules.IsInvertible 𝓝) :
    ∃ M : RigidifiedLineBundle f (L.one (𝟙 (Spec (CommRingCat.of S)))) (𝟙 (Spec (CommRingCat.of S))),
      ∀ (S' : Type) [CommRing S'] (φ : S →+* S') {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of S')} (g : A' ⟶ A),
        IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)) →
        (LocIsoOnBase f' ((Scheme.Modules.pullback g).obj 𝓜) ((Scheme.Modules.pullback g).obj 𝓝) ↔
          Nonempty ((M.pullbackAlong (⟨Spec.map (CommRingCat.ofHom φ), Category.comp_id _⟩ :
              SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) (𝟙 (Spec (CommRingCat.of S))))).L ≅
            (RigidifiedLineBundle.unit (c := f) (ε := L.one (𝟙 (Spec (CommRingCat.of S)))) (Spec.map (CommRingCat.ofHom φ))).L)) := by sorry

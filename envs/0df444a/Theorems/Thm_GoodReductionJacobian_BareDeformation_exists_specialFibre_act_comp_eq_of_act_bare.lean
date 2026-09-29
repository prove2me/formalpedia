-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_specialFibre_act_comp_eq_of_act_bare
-- name    : GoodReductionJacobian.BareDeformation.exists_specialFibre_act_comp_eq_of_act_bare
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/27079276-e726-5e8f-b715-10b3aa5a43b8
-- title:
--   Λ-action on the special fibre of a bare deformation
-- statement:
--   Let $S$ be a commutative local ring, $S_0$ a commutative $S$-algebra such that $\operatorname{alg}_{S\to S_0}$ is surjective with kernel contained in the maximal ideal of $S$, and let $\Lambda$ be a ring. Let $f_0 : A_0 \to \operatorname{Spec} S_0$ be a morphism of schemes equipped with a relative group law $L_0$, i.e. a functorial group structure on the sets $\mathrm{SchemeHomOver}\, t\, f_0$ of $T$-points over $\operatorname{Spec} S_0$. Let $\mathrm{act}_0 : \Lambda \to \operatorname{End}(A_0)$ satisfy: $\mathrm{act}_0\,x$ followed by $f_0$ is $f_0$; composition with $\mathrm{act}_0\,x$ carries $L_0$-products of points to products of the composites; $\mathrm{act}_0\,1 = \mathrm{id}$; $\mathrm{act}_0(xy) = \mathrm{act}_0\,y$ followed by $\mathrm{act}_0\,x$; and $P$ followed by $\mathrm{act}_0(x+y)$ is the $L_0$-product of $P \gg \mathrm{act}_0\,x$ and $P \gg \mathrm{act}_0\,y$. Let $D_0$ be a `BareDeformation` of $(f_0,L_0)$ over $S$: a scheme with morphism $D_0.f$ to $\operatorname{Spec} S$, a commutative relative group law $D_0.L$, an abelian-scheme property bundle, and $D_0.g : A_0 \to D_0.A$ making the square over $\operatorname{Spec} S_0 \to \operatorname{Spec} S$ cartesian and compatible with the laws. Write $X_\kappa$ for the pullback of $D_0.f$ along $\operatorname{Spec}$ of $S \to \mathrm{ResidueField}\, S$, with projections $\mathrm{pr}_1,\mathrm{pr}_2$, and $L_\kappa$ for the base change of $D_0.L$. Then there exist $j_\kappa : X_\kappa \to A_0$ with $j_\kappa \gg D_0.g = \mathrm{pr}_1$ and $\psi : \Lambda \to \operatorname{End}(X_\kappa)$ with $\psi\,x \gg \mathrm{pr}_2 = \mathrm{pr}_2$, such that $\psi\,x \gg j_\kappa = j_\kappa \gg \mathrm{act}_0\,x$; each $\psi\,x$ carries $L_\kappa$-products of points to products of their images under `pushPt`; $\psi\,1 = \mathrm{id}$; $\psi(xy) = \psi\,y \gg \psi\,x$; and $P \gg \psi(x+y)$ is the $L_\kappa$-product of $P \gg \psi\,x$ and $P \gg \psi\,y$.
--
--   This is the transport of a ring action by group-law endomorphisms from the scheme $A_0$ over $S_0$ to the special fibre of a bare deformation over the local ring $S$, together with the compatibility morphism $j_\kappa$ identifying the special fibre with the base change of $A_0$ to the residue field. It is used in the study of endomorphism actions on special fibres of deformations, where the $\psi$-package provides the residue-field action induced by an action in characteristic of the closed point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_exists_specialFibre_act_comp_eq_of_act_bare.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_GoodReductionJacobian_IsRegluingBy
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPair
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAt
import Definitions.Def_Algebra_PointDerivations
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal IsLocalRing Scheme.TwoAffineOpenCover
open scoped Quaternion TensorProduct NumberField

theorem GoodReductionJacobian.BareDeformation.exists_specialFibre_act_comp_eq_of_act_bare
    (S S₀ : Type) [CommRing S] [IsLocalRing S] [CommRing S₀] [Algebra S S₀]
    (hπ : Function.Surjective (algebraMap S S₀)) (hI : RingHom.ker (algebraMap S S₀) ≤ maximalIdeal S)
    {Λ : Type} [Ring Λ]
    {A₀ : Scheme.{0}} {f₀ : A₀ ⟶ Spec (CommRingCat.of S₀)} (L₀ : RelativeGroupLaw S₀ f₀)

    (act₀ : Λ → (A₀ ⟶ A₀)) (act₀_over : ∀ x : Λ, act₀ x ≫ f₀ = f₀)
    (act₀_hom : ∀ (x : Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S₀)) (P Q : SchemeHomOver t f₀),
      (L₀.mul t P Q).1 ≫ act₀ x =
        (L₀.mul t ⟨P.1 ≫ act₀ x, by rw [Category.assoc, act₀_over, P.2]⟩
          ⟨Q.1 ≫ act₀ x, by rw [Category.assoc, act₀_over, Q.2]⟩).1)
    (act₀_one : act₀ 1 = 𝟙 A₀)
    (act₀_mul : ∀ x y : Λ, act₀ (x * y) = act₀ y ≫ act₀ x)
    (act₀_add : ∀ (x y : Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S₀)) (P : SchemeHomOver t f₀),
      P.1 ≫ act₀ (x + y) =
        (L₀.mul t ⟨P.1 ≫ act₀ x, by rw [Category.assoc, act₀_over, P.2]⟩
          ⟨P.1 ≫ act₀ y, by rw [Category.assoc, act₀_over, P.2]⟩).1)
    (D₀ : BareDeformation f₀ L₀ S) :

    ∃ (jκ : (pullback D₀.f (specMap S (ResidueField S))) ⟶ A₀) (hjκ : jκ ≫ D₀.g = (pullback.fst D₀.f (specMap S (ResidueField S))))
      (ψ : Λ → ((pullback D₀.f (specMap S (ResidueField S))) ⟶ (pullback D₀.f (specMap S (ResidueField S)))))
      (hψ : ∀ x : Λ, ψ x ≫ (pullback.snd D₀.f (specMap S (ResidueField S))) = (pullback.snd D₀.f (specMap S (ResidueField S)))),
      (∀ x : Λ, ψ x ≫ jκ = jκ ≫ act₀ x) ∧
      (∀ (x : Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (ResidueField S))) (P Q : SchemeHomOver t (pullback.snd D₀.f (specMap S (ResidueField S)))),
        pushPt (ψ x) (hψ x) ((RelativeGroupLaw.baseChange (specMap S (ResidueField S)) D₀.L).mul t P Q) = (RelativeGroupLaw.baseChange (specMap S (ResidueField S)) D₀.L).mul t (pushPt (ψ x) (hψ x) P) (pushPt (ψ x) (hψ x) Q)) ∧
      ψ 1 = 𝟙 (pullback D₀.f (specMap S (ResidueField S))) ∧
      (∀ x y : Λ, ψ (x * y) = ψ y ≫ ψ x) ∧
      (∀ (x y : Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (ResidueField S))) (P : SchemeHomOver t (pullback.snd D₀.f (specMap S (ResidueField S)))),
        P.1 ≫ ψ (x + y) =
          ((RelativeGroupLaw.baseChange (specMap S (ResidueField S)) D₀.L).mul t ⟨P.1 ≫ ψ x, by rw [Category.assoc, hψ, P.2]⟩
            ⟨P.1 ≫ ψ y, by rw [Category.assoc, hψ, P.2]⟩).1) := by sorry

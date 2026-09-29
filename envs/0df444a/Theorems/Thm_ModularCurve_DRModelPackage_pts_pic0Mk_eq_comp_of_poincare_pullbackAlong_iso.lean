-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackage_pts_pic0Mk_eq_comp_of_poincare_pullbackAlong_iso
-- name    : ModularCurve.DRModelPackage.pts_pic0Mk_eq_comp_of_poincare_pullbackAlong_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/ab82d54c-8894-53ee-a426-b18859388d51
-- title:
--   Recognising pts of a divisor class from its Poincaré fibre
-- statement:
--   Let $p$ be a prime and $\mathfrak X$ a `DRModelPackage p`, with integral model $f =$ `DRModel.toBase p` over $\operatorname{Spec}\mathbb Z$, assumed proper, and section $\varepsilon_{\infty} = \mathfrak X.\varepsilon_{\inf}$. Let $D$ be a relative $\mathrm{Pic}^0$ designation for $f$ (a scheme $D.P$ over $\operatorname{Spec}\mathbb Z$ with a zero section) and let $h_D$ witness that $D$ represents the functor of $\varepsilon_\infty$-rigidified line bundles on $f$ whose geometric fibres are algebraically equivalent to zero, with Poincaré bundle $h_D.\mathrm{poincare}$ over $D.\mathrm{toBase}$. Assume further: a $\overline{\mathbb Q}$-point $\bar\varepsilon$ of the geometric curve model $\mathfrak X.M_\eta$; a morphism $aj : \mathfrak X.M_\eta.C \to D.P$ lying over $\operatorname{Spec}\overline{\mathbb Q} \to \operatorname{Spec}\mathbb Z$ (`haj_over`); the corresponding representability $h'$ for the base change of $f$ and of $\varepsilon_\infty$ to $\mathbb Q$ together with a morphism $aj_{\mathbb Q}$ from the curve over $\mathbb Q$ to $(D.\mathrm{baseChange}\ \mathbb Q).P$ over $\mathbb Q$; an isomorphism between the $\mathbb Q$-Poincaré bundle of $h'$ and the descent of the pullback of $h_D.\mathrm{poincare}$ along $\mathrm{pullback.fst}$ (`hP`); the normalisation that for every field $K$, every $t : \operatorname{Spec} K \to \operatorname{Spec}\mathbb Q$ and every $K$-point $x$ of the curve over $\mathbb Q$ above $t$, the pullback of the $\mathbb Q$-Poincaré bundle along $x$ followed by $aj_{\mathbb Q}$ is isomorphic to the line bundle of the degree-one relative Cartier divisor of $x$ tensored with the ideal module of the divisor cut out by $t$ followed by the base-changed section $\varepsilon_\infty$ (`hajQ`); and a factorisation of $aj$ as $\mathfrak X.e_\eta$ followed by a compatible comparison $k_0$ of the $\overline{\mathbb Q}$- and $\mathbb Q$-base changes, then $aj_{\mathbb Q}$, then the projection $\mathrm{pullback.fst}$ (`hk₀`). Finally let $\mathrm{pts}$ be a bijection from $\mathrm{JZero}\ p = \mathrm{Pic}^0$ of the geometric modular function field $\mathrm{modularFunctionFieldBar}\ p$ onto the $\overline{\mathbb Q}$-points of $D.\mathrm{toBase}$, additive for the relative group law attached to $h_D$ via the fibrewise algebraic-equivalence cut (`pts_add`), and such that for each $\overline{\mathbb Q}$-point $x$ of $\mathfrak X.M_\eta.C$ there is a degree-zero divisor equal to $[v_x] - [v_{\bar\varepsilon}]$, in terms of the place attached to a point by `pointEquivPlace`, whose class is sent by $\mathrm{pts}$ to $x$ followed by $aj$ (`pts_aj`). Now let $O$ be a commutative ring, $z$ an $O$-point of $D.\mathrm{toBase}$ over $\mathbb Z$, and $tb : \operatorname{Spec}\overline{\mathbb Q} \to \operatorname{Spec} O$ a morphism over $\operatorname{Spec}\mathbb Z$. Let $m \in \mathbb N$, let $q_0,\dots,q_{m-1}$ be $\overline{\mathbb Q}$-points of $\mathfrak X.M_\eta.C$, let $\mathrm{pos}_j, \mathrm{neg}_j \in \mathbb N$ with $\sum_j(\mathrm{pos}_j - \mathrm{neg}_j) = 0$, and let $D_x$ be a degree-zero divisor equal to $\sum_j (\mathrm{pos}_j - \mathrm{neg}_j)\,[v_{q_j}]$. Assume that the pullback of $h_D.\mathrm{poincare}$ along the $\overline{\mathbb Q}$-point $tb$ followed by $z$ has underlying module isomorphic to the iterated tensor product, folded over `List.finRange m` ending at the unit object, of $(\mathcal I_{q_j}^{\mathrm{pos}_j})^{\vee} \otimes \mathcal I_{q_j}^{\mathrm{neg}_j}$, where $\mathcal I_{q}$ denotes the ideal sheaf of the degree-one relative Cartier divisor cut out by the graph of $q$ in the $\overline{\mathbb Q}$-base change of the integral model, taken through $\mathfrak X.e_\eta$. Then $\mathrm{pts}$ of the class of $D_x$ is, as a morphism, $tb$ followed by $z$.
--
--   This is the recognition step for the Abel–Jacobi parametrisation: it converts the knowledge that the Poincaré fibre at an integral point of the relative $\mathrm{Pic}^0$ scheme is, on the geometric generic fibre, the line bundle attached to a prescribed degree-zero combination of points into the identity of points asserting that the prescribed divisor class is exactly that point. It is used in the proof of [`ModularCurve.DRModelPackage.exists_schemeHomOver_of_comp_eq_zero_of_abelJacobiPin_of_surjective`](thm.html#ModularCurve.DRModelPackage.exists_schemeHomOver_of_comp_eq_zero_of_abelJacobiPin_of_surjective).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackage_pts_pic0Mk_eq_comp_of_poincare_pullbackAlong_iso.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_ModularCurve_DRModelLegTwoInput
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_LevelOneGlueData
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_ModularCurve_ModularUnit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  ModularCurve AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve
open AlgebraicCurve IsLocalRing ModularCurve.PlaceSpecialization

set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.DRModelPackage.pts_pic0Mk_eq_comp_of_poincare_pullbackAlong_iso
    (p : ℕ) [Fact p.Prime]
    (𝔛 : DRModelPackage p)
    (D : RelativePic0Designation ℤ (DRModel.toBase p))
    (hD : RepresentsRelSubPic (DRModel.toBase p) 𝔛.εinf (algEquivZeroCut (DRModel.toBase p) 𝔛.εinf) D)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Mη.C // q ≫ 𝔛.Mη.toBase = 𝟙 _})
    (aj : 𝔛.Mη.C ⟶ D.P)
    [IsProper (DRModel.toBase p)]
    (h' : RepresentsRelSubPic (baseChange ℤ (DRModel.toBase p) ℚ) (sectionBaseChange ℚ 𝔛.εinf)
          (algEquivZeroCut (baseChange ℤ (DRModel.toBase p) ℚ) (sectionBaseChange ℚ 𝔛.εinf)) (D.baseChange ℚ))
    (ajQ : SchemeHomOver (baseChange ℤ (DRModel.toBase p) ℚ) (D.baseChange ℚ).toBase)
    (hP : Nonempty (h'.poincare.L ≅ (BaseChange.ofR (DRModel.toBase p) 𝔛.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap ℤ ℚ), pullback.condition⟩)).L))
    (hajQ : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
        (x : SchemeHomOver t (baseChange ℤ (DRModel.toBase p) ℚ)),
      Nonempty ((h'.poincare.pullbackAlong
          ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange ℤ (DRModel.toBase p) ℚ) x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange ℤ (DRModel.toBase p) ℚ) (t ≫ (sectionBaseChange ℚ 𝔛.εinf).1)
            ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔛.εinf).2).trans
              (Category.comp_id t)))).idealModule))
    (hk₀ : ∃ k₀ : pullback (DRModel.toBase p) (specMap ℤ (AlgebraicClosure ℚ)) ⟶ pullback (DRModel.toBase p) (specMap ℤ ℚ),
        k₀ ≫ pullback.fst (DRModel.toBase p) (specMap ℤ ℚ) = pullback.fst (DRModel.toBase p) (specMap ℤ (AlgebraicClosure ℚ)) ∧
        k₀ ≫ pullback.snd (DRModel.toBase p) (specMap ℤ ℚ) =
          pullback.snd (DRModel.toBase p) (specMap ℤ (AlgebraicClosure ℚ)) ≫ specMap ℚ (AlgebraicClosure ℚ) ∧
        aj = 𝔛.eη ≫ k₀ ≫ ajQ.1 ≫ pullback.fst D.toBase (specMap ℤ ℚ))
    (haj_over : aj ≫ D.toBase = 𝔛.Mη.toBase ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))
    (pts : JZero p ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) D.toBase)
    (pts_add : ∀ x y : JZero p, pts (x + y) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf) hD).mul _ (pts x) (pts y))
    (pts_aj : ∀ x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Mη.C // q ≫ 𝔛.Mη.toBase = 𝟙 _},
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar p)),
        (Dv : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar p)) =
          Finsupp.single (𝔛.Mη.pointEquivPlace x) 1 - Finsupp.single (𝔛.Mη.pointEquivPlace εbar) 1 ∧
        (pts (Pic0.mk Dv)).1 = x.1 ≫ aj)

    (O : Type) [CommRing O] (z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) D.toBase)
    (tb : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of O))
    (htb : tb ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ O)) = Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))
    (m : ℕ) (q : Fin m → {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Mη.C // q ≫ 𝔛.Mη.toBase = 𝟙 _})
    (pos neg : Fin m → ℕ) (hn : (∑ j, ((pos j : ℤ) - (neg j : ℤ))) = 0)
    (Dx : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar p))))
    (hDxq : (Dx : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar p)) =
      ∑ j, Finsupp.single (𝔛.Mη.pointEquivPlace (q j)) ((pos j : ℤ) - (neg j : ℤ)))
    (hzgen : Nonempty ((hD.poincare.pullbackAlong ⟨tb ≫ z.1, by rw [Category.assoc, z.2, htb]⟩).L ≅
      (List.finRange m).foldr (fun j M =>
          ((RelEffCartierDiv.ofPoint (DRModel.toBase p) ((q j).1 ≫ 𝔛.eη ≫ pullback.fst (DRModel.toBase p) _)
              (by rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% 𝔛.heη, reassoc_of% (q j).2])).I ^ (pos j)).invModule ⊗
          ((RelEffCartierDiv.ofPoint (DRModel.toBase p) ((q j).1 ≫ 𝔛.eη ≫ pullback.fst (DRModel.toBase p) _)
              (by rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% 𝔛.heη, reassoc_of% (q j).2])).I ^ (neg j)).module ⊗ M)
        (𝟙_ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))).Modules))) :
    (pts (Pic0.mk Dx)).1 = tb ≫ z.1 := by sorry

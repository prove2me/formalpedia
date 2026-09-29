-- Prove2me | Theorems.Thm_ModularCurve_XOne_pic0Correspondence_pts_eq_comp_of_poincare_pullbackAlong_iso_laurentBaseChange
-- name    : ModularCurve.XOne.pic0Correspondence_pts_eq_comp_of_poincare_pullbackAlong_iso_laurentBaseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/df5ff09a-4d2e-50d5-a561-c60de9157f46
-- title:
--   Correspondence α_*β^* on J₁(N) realised by an endomorphism
-- statement:
--   Let $L$ be a field of characteristic zero equipped with an algebra map $L \to \overline{\mathbb{Q}}$, let $N \ge 1$, and let $c : X \to \operatorname{Spec} L$ be proper, smooth of relative dimension one and geometrically integral, with a section $\varepsilon$. Let $D$ consist of a scheme $P$ over $\operatorname{Spec} L$ with a zero section, and let $h$ witness that $P$ represents the functor of $\varepsilon$-rigidified invertible modules on $X \times_L T$ that are fibrewise algebraically equivalent to zero, with Poincaré bundle `h.poincare`. Let $aj : X \to P$ be a morphism over $L$ with $\varepsilon \,$ followed by $aj$ the zero section, such that for every field $K$, every $t : \operatorname{Spec} K \to \operatorname{Spec} L$ and every $K$-point $x$ of $X$ over $t$, the pullback of `h.poincare` along $x$ followed by $aj$ is isomorphic to the line bundle of the relative effective Cartier divisor at $x$ tensored with the ideal module of the divisor at $t$ followed by $\varepsilon$. Let $M_\eta$ be a curve model over $\overline{\mathbb{Q}}$ of the Laurent base change $\overline{\mathbb{Q}}\cdot\mathbb{Q}(X_1(N))$ together with an isomorphism $e_\eta : M_\eta.C \cong X \times_L \overline{\mathbb{Q}}$ over $\overline{\mathbb{Q}}$; let $F_0' \subseteq \mathbb{Q}((q))$ be an intermediate field and $M_\eta'$ a curve model of $\overline{\mathbb{Q}}\cdot F_0'$ with an isomorphism $e_\eta'$ onto $Y \times_L \overline{\mathbb{Q}}$, where $cY : Y \to \operatorname{Spec} L$ carries two morphisms $\pi_\alpha, \pi_\beta : Y \to X$ over $L$, both finite, flat and locally of finite presentation, with $\pi_\alpha$ of constant fibre rank $d$. Let $\varphi : P \to P$ be a morphism over $L$ which is additive for the relative group law carried by $h$, and such that for every $\overline{\mathbb{Q}}$-point $z$ of $P$ over $L$ the pullback of `h.poincare` along $z$ followed by $\varphi$ is isomorphic to the $\varepsilon$-rigidification of the norm module, in rank $d$, along the base change of $\pi_\alpha$ of the pullback along the base change of $\pi_\beta$ of the bundle associated with $z$. Let $\alpha, \beta : \overline{\mathbb{Q}}\cdot\mathbb{Q}(X_1(N)) \to \overline{\mathbb{Q}}\cdot F_0'$ be $\overline{\mathbb{Q}}$-algebra maps that are integral as ring maps, compatible with $\pi_\alpha$ respectively $\pi_\beta$ on $\overline{\mathbb{Q}}$-points in the sense that the place of $x$ is the restriction along $\alpha$ (respectively $\beta$) of the place of $y$ whenever $y$ maps to $x$; assume the top field has principal divisors of degree zero, the fundamental identity holds along $\beta$, the extension along $\alpha$ is module-finite and the pushforward norm formula holds along $\alpha$. Finally let $pts$ be a bijection from $\mathrm{Pic}^0(\overline{\mathbb{Q}}\cdot\mathbb{Q}(X_1(N)))$ onto the $\overline{\mathbb{Q}}$-points of $P$ over $L$ which is additive for the relative group law and which sends, for $\overline{\mathbb{Q}}$-points $x$ and $s$ of $M_\eta.C$ with $s$ corresponding to $\varepsilon$, the class of a degree-zero divisor equal to $(x) - (s)$ to the point $x$ followed by $e_\eta$, the first projection and $aj$. Then for every $x \in \mathrm{Pic}^0(\overline{\mathbb{Q}}\cdot\mathbb{Q}(X_1(N)))$ the point $pts$ of the image of $x$ under the correspondence $\alpha_* \beta^*$ equals $pts(x)$ followed by $\varphi$.
--
--   This identifies the divisor-theoretic correspondence $\alpha_*\beta^*$ on the degree-zero divisor class group of the function field of $X_1(N)$ over $\overline{\mathbb{Q}}$ with composition by an endomorphism of the scheme representing the relative $\mathrm{Pic}^0$, the endomorphism being specified by the norm-of-pullback recipe on the Poincaré bundle. It is the form in which Hecke correspondences are transported to the representing object, and is used in the construction of Hecke operators on the two-chart model of $X_1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOne_pic0Correspondence_pts_eq_comp_of_poincare_pullbackAlong_iso_laurentBaseChange.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian ModularCurve AlgebraicCurve AlgebraicGeometry.SmoothProperCurve

theorem ModularCurve.XOne.pic0Correspondence_pts_eq_comp_of_poincare_pullbackAlong_iso_laurentBaseChange

    (L : Type) [Field L] [CharZero L] [Algebra L (AlgebraicClosure ℚ)]
    (N : ℕ) [NeZero N]
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of L)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of L))) c)
    (D : RelativePic0Designation L c)
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (aj : SchemeHomOver c D.toBase) (hajε : ε.1 ≫ aj.1 = D.zeroSection)
    (haj : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of L)) (x : SchemeHomOver t c),
        Nonempty ((h.poincare.pullbackAlong
            ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩).L ≅
          (RelEffCartierDiv.ofPoint c x.1 x.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint c (t ≫ ε.1)
              ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t)))).idealModule))

    (Mη : CurveModel (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar N))
    (eη : Mη.C ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure ℚ))))) [IsIso eη]
    (heη : eη ≫ pullback.snd c _ = Mη.toBase)

    (F₀' : IntermediateField ℚ (LaurentSeries ℚ))

    (Y : Scheme.{0}) (cY : Y ⟶ Spec (CommRingCat.of L))
    (πα πβ : Y ⟶ X) (hα : πα ≫ c = cY) (hβ : πβ ≫ c = cY)
    [IsFinite πα] [Flat πα] [LocallyOfFinitePresentation πα]
    [IsFinite πβ] [Flat πβ] [LocallyOfFinitePresentation πβ]
    (d : ℕ) (hdα : ∀ y, πα.finrank y = d)

    (φη : SchemeHomOver D.toBase D.toBase)
    (hφpt : ∀ z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure ℚ)))) D.toBase,
      Nonempty ((h.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp z φη)).L ≅
        Scheme.Modules.rigidify (rigSection c (Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure ℚ)))) ε)
          (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure ℚ)))))
          (Scheme.Modules.normModule
            (curveChange πα hα (Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure ℚ))))) d
            ((Scheme.Modules.pullback
              (curveChange πβ hβ (Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure ℚ)))))).obj
              (h.poincare.pullbackAlong z).L))))
    (hφadd : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of L)) (x y : SchemeHomOver s D.toBase),
      NeronModelInfra.schemeHomOverComp
          ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul s x y) φη =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul s
          (NeronModelInfra.schemeHomOverComp x φη) (NeronModelInfra.schemeHomOverComp y φη))

    (Mη' : CurveModel (AlgebraicClosure ℚ) (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) F₀'))
    (eη' : Mη'.C ⟶ pullback cY (Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure ℚ))))) [IsIso eη']
    (heη' : eη' ≫ pullback.snd _ _ = Mη'.toBase)
    (α : ModularCurve.x1FunctionFieldBar N →ₐ[AlgebraicClosure ℚ] ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) F₀') (hαI : α.toRingHom.IsIntegral)
    (β : ModularCurve.x1FunctionFieldBar N →ₐ[AlgebraicClosure ℚ] ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) F₀') (hβI : β.toRingHom.IsIntegral)
    (hplaceα : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη'.C // q ≫ Mη'.toBase = 𝟙 _})
        (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      y.1 ≫ eη' ≫ pullback.fst cY _ ≫ πα = x.1 ≫ eη ≫ pullback.fst c _ →
      Mη.pointEquivPlace x =
        Place.restrictAlong α hαI (Mη'.pointEquivPlace y))
    (hplaceβ : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη'.C // q ≫ Mη'.toBase = 𝟙 _})
        (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      y.1 ≫ eη' ≫ pullback.fst cY _ ≫ πβ = x.1 ≫ eη ≫ pullback.fst c _ →
      Mη.pointEquivPlace x =
        Place.restrictAlong β hβI (Mη'.pointEquivPlace y))

    [hPD : HasPrincipalDivisors (AlgebraicClosure ℚ) (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) F₀')]
    (hFI : FundamentalIdentityAlong (AlgebraicClosure ℚ) β hβI) (hfin : FiniteAlong (AlgebraicClosure ℚ) α)
    (hN : NormFormulaAlong (AlgebraicClosure ℚ) α hfin)

    (pts : ModularCurve.JOne N ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure ℚ)))) D.toBase)
    (hadd : ∀ x y : ModularCurve.JOne N,
      pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul _ (pts x) (pts y))
    (hnorm : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      s.1 ≫ eη ≫ pullback.fst c _ = Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure ℚ))) ≫ ε.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ModularCurve.x1FunctionFieldBar N),
        (Dv : Divisor (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar N)) =
          Finsupp.single (Mη.pointEquivPlace x) 1 - Finsupp.single (Mη.pointEquivPlace s) 1 ∧
        (pts (Pic0.mk Dv)).1 = x.1 ≫ eη ≫ pullback.fst c _ ≫ aj.1)
    (x : ModularCurve.JOne N) :
    (pts (Pic0.correspondence β α hβI hαI hFI hfin hN x)).1 = (pts x).1 ≫ φη.1 := by sorry

-- Prove2me | Theorems.Thm_ModularCurve_XH_pic0Correspondence_pts_eq_comp_of_poincare_pullbackAlong_iso_laurentBaseChange
-- name    : ModularCurve.XH.pic0Correspondence_pts_eq_comp_of_poincare_pullbackAlong_iso_laurentBaseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/f2ae64d3-73f9-50f1-a2ff-5a28edfc60c8
-- title:
--   Correspondence α_*β^* on J_H induced by an endomorphism
-- statement:
--   Let $L$ be a field of characteristic $0$ equipped with an $L$-algebra structure on $\bar{\mathbb Q}$, let $M$ be a nonzero natural number and $H \le (\mathbb Z/M)^{\times}$. Let $c : X \to \operatorname{Spec} L$ be proper, smooth of relative dimension one and geometrically integral, with a section $\varepsilon$, and let $D$ consist of a scheme $P$ over $\operatorname{Spec} L$ with a zero section; $h$ asserts that $D$, with a rigidified line bundle $\mathcal P$ on $X \times_L P$ satisfying the fibrewise algebraic-equivalence-to-zero condition, represents the functor of $\varepsilon$-rigidified line bundles with that condition, $\mathcal P$ being trivial along the zero section. A morphism $\mathrm{aj} : X \to P$ over $L$ is given with $\varepsilon$ followed by $\mathrm{aj}$ equal to the zero section, and with the Abel–Jacobi property `haj`: for every field $K$, every $t : \operatorname{Spec} K \to \operatorname{Spec} L$ and every $K$-point $x$ of $X$ over $t$, the pullback of $\mathcal P$ along $x$ followed by $\mathrm{aj}$ is isomorphic to the line bundle of the relative effective Cartier divisor of $x$ tensored with the ideal module of the divisor of $t$ followed by $\varepsilon$. Further data: a curve model $M_\eta$ over $\bar{\mathbb Q}$ of [`ModularCurve.xHFunctionFieldBar M H`](def/ModularCurve_XH.html#L123) with an isomorphism $e_\eta$ onto $X \times_L \bar{\mathbb Q}$ respecting the structure morphisms; an intermediate field $F_0'$ of $\mathbb Q \subseteq \mathbb Q((q))$; a scheme $Y$ over $L$ with two morphisms $\pi_\alpha, \pi_\beta : Y \to X$ over $L$, each finite, flat and locally of finite presentation, $\pi_\alpha$ of constant fibre rank $d$; a curve model $M_\eta'$ over $\bar{\mathbb Q}$ of [`ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) F₀'`](def/ModularCurve_LaurentCoeff.html#L103) with an isomorphism $e_\eta'$ onto $Y \times_L \bar{\mathbb Q}$; an endomorphism $\varphi_\eta$ of $P$ over $L$ which is additive for the relative group law supplied by $h$ (hypothesis `hφadd`) and which, on every $\bar{\mathbb Q}$-point $z$ of $P$, sends the pullback of $\mathcal P$ along $z$ to the rigidification along the base-changed section $\varepsilon$ of the rank-$d$ norm module along the base change of $\pi_\alpha$ of the pullback along the base change of $\pi_\beta$ of that bundle (hypothesis `hφpt`); two $\bar{\mathbb Q}$-algebra maps $\alpha, \beta$ from `xHFunctionFieldBar M H` to `laurentBaseChange (AlgebraicClosure ℚ) F₀'`, both integral, such that on $\bar{\mathbb Q}$-points $\pi_\alpha$, respectively $\pi_\beta$, realises restriction of places along $\alpha$, respectively $\beta$; the existence of principal divisors for the upper field, the fundamental identity along $\beta$, finiteness along $\alpha$ and the pushforward norm formula along $\alpha$; and finally a bijection `pts` between $J_H = \mathrm{Pic}^0$ of `xHFunctionFieldBar M H` and the $\bar{\mathbb Q}$-points of $P$ over $L$, additive for the relative group law, and compatible with Abel–Jacobi in the sense that for $\bar{\mathbb Q}$-points $x, s$ of $M_\eta$ with $s$ corresponding to the base change of $\varepsilon$ there is a degree-zero divisor equal to $(\mathrm{place}\,x) - (\mathrm{place}\,s)$ whose class is carried by `pts` to $x$ followed by $e_\eta$, the first projection and $\mathrm{aj}$. The conclusion is that for every $x \in J_H$, the point `pts` of the class $\alpha_*\beta^*x$, namely `Pic0.correspondence β α … x`, equals the point `pts x` followed by $\varphi_\eta$.
--
--   This is the dictionary statement identifying the divisorial correspondence $\alpha_* \circ \beta^*$ on the degree-zero divisor class group of the function field of $X_H(M)$ with an endomorphism of the representing $\mathrm{Pic}^0$-scheme over $L$, characterised by the norm of the pulled-back Poincaré bundle. It is used in the construction of Hecke operators on models of $X_H$ at a prime and in the corresponding Néron-model statements.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XH_pic0Correspondence_pts_eq_comp_of_poincare_pullbackAlong_iso_laurentBaseChange.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_XH
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

theorem ModularCurve.XH.pic0Correspondence_pts_eq_comp_of_poincare_pullbackAlong_iso_laurentBaseChange

    (L : Type) [Field L] [CharZero L] [Algebra L (AlgebraicClosure ℚ)]
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
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

    (Mη : CurveModel (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H))
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
    (α : ModularCurve.xHFunctionFieldBar M H →ₐ[AlgebraicClosure ℚ] ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) F₀') (hαI : α.toRingHom.IsIntegral)
    (β : ModularCurve.xHFunctionFieldBar M H →ₐ[AlgebraicClosure ℚ] ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) F₀') (hβI : β.toRingHom.IsIntegral)
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

    (pts : ModularCurve.JH M H ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure ℚ)))) D.toBase)
    (hadd : ∀ x y : ModularCurve.JH M H,
      pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul _ (pts x) (pts y))
    (hnorm : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      s.1 ≫ eη ≫ pullback.fst c _ = Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure ℚ))) ≫ ε.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ModularCurve.xHFunctionFieldBar M H),
        (Dv : Divisor (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H)) =
          Finsupp.single (Mη.pointEquivPlace x) 1 - Finsupp.single (Mη.pointEquivPlace s) 1 ∧
        (pts (Pic0.mk Dv)).1 = x.1 ≫ eη ≫ pullback.fst c _ ≫ aj.1)
    (x : ModularCurve.JH M H) :
    (pts (Pic0.correspondence β α hβI hαI hFI hfin hN x)).1 = (pts x).1 ≫ φη.1 := by sorry

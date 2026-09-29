-- Prove2me | Theorems.Thm_ModularCurve_pic0Correspondence_pts_eq_comp_of_poincare_pullbackAlong_iso
-- name    : ModularCurve.pic0Correspondence_pts_eq_comp_of_poincare_pullbackAlong_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/b2b42e36-f9c8-5841-856b-ea19db438556
-- title:
--   Divisor correspondence agrees with classifying endomorphism on ℚ̄-points
-- statement:
--   Fix $N \ge 1$ and a scheme $X$ with a structure morphism $c \colon X \to \operatorname{Spec}\mathbb{Q}$ that is proper, smooth of relative dimension $1$ and geometrically integral, together with a section $\varepsilon$ of $c$. Let $D$ consist of a scheme $D.P$ over $\mathbb{Q}$ with a zero section, and let $h$ exhibit $D$ as representing the functor of $\varepsilon$-rigidified line bundles on $X \times_{\mathbb{Q}} T$ whose fibres over algebraically closed fields are algebraically equivalent to zero, with Poincaré bundle `h.poincare`. Let $aj \colon X \to D.P$ be a morphism over $\mathbb{Q}$ with $\varepsilon$ followed by $aj$ equal to the zero section, and assume that for every field $K$, every $t \colon \operatorname{Spec} K \to \operatorname{Spec}\mathbb{Q}$ and every $K$-point $x$ of $X$ over $t$ the pullback of the Poincaré bundle along $x$ followed by $aj$ is isomorphic to the inverse ideal module of the graph of $x$ tensored with the ideal module of the graph of $t$ followed by $\varepsilon$, i.e. to $\mathcal{O}(x - \varepsilon)$. Let $M_\eta$ be a curve model over $\overline{\mathbb{Q}}$ of the base-changed level-$N$ modular function field $\overline{\mathbb{Q}}\cdot F_N$, identified by an isomorphism $e_\eta$ with $X \times_{\mathbb{Q}} \overline{\mathbb{Q}}$ compatibly with the base morphisms. Fix $M' \ge 1$, a second curve $Y \to \operatorname{Spec}\mathbb{Q}$ and two morphisms $\pi_\alpha, \pi_\beta \colon Y \to X$ over $\mathbb{Q}$, each finite, flat and locally of finite presentation, with $\pi_\alpha$ of constant fibre rank $d$. Let $\varphi_\eta \colon D.P \to D.P$ be a morphism over $\mathbb{Q}$ such that (i) for every $\overline{\mathbb{Q}}$-point $z$ of $D.P$ the pullback of the Poincaré bundle along $z$ followed by $\varphi_\eta$ is isomorphic to the rigidification along the section induced by $\varepsilon$ of the rank-$d$ norm module along the base change of $\pi_\alpha$ of the pullback along the base change of $\pi_\beta$ of the pullback of the Poincaré bundle along $z$, and (ii) $\varphi_\eta$ is compatible with the relative group law on $D.P$ furnished by $h$. Let $M'_\eta$ be a curve model over $\overline{\mathbb{Q}}$ of $\overline{\mathbb{Q}}\cdot F_{M'}$, identified with $Y \times_{\mathbb{Q}} \overline{\mathbb{Q}}$, and let $\alpha, \beta \colon \overline{\mathbb{Q}}\cdot F_N \to \overline{\mathbb{Q}}\cdot F_{M'}$ be $\overline{\mathbb{Q}}$-algebra maps along which the target is integral, such that on $\overline{\mathbb{Q}}$-points $\pi_\alpha$ (respectively $\pi_\beta$) realises restriction of places along $\alpha$ (respectively $\beta$). Assume further that every nonzero function at level $M'$ has a principal divisor of degree zero, that the fundamental identity $\sum_w e_w f_w = [F':F]$ holds along $\beta$, and that $\overline{\mathbb{Q}}\cdot F_{M'}$ is finite along $\alpha$ with the pushforward norm formula. Finally, let `pts` be a bijection from $\operatorname{Pic}^0(\overline{\mathbb{Q}}\cdot F_N)$ to the $\overline{\mathbb{Q}}$-points of $D.P$ which is additive for the relative group law, and which sends the class of $[x] - [s]$, for $\overline{\mathbb{Q}}$-points $x$ and $s$ of $M_\eta.C$ with $s$ corresponding to $\varepsilon$, to the point $x$ followed by $e_\eta$, the first projection and $aj$. Then for every class $x$ in $\operatorname{Pic}^0(\overline{\mathbb{Q}}\cdot F_N)$ the point `pts` of the image of $x$ under the correspondence given by pulling back along $\beta$ and pushing forward along $\alpha$ equals the point `pts x` followed by $\varphi_\eta$.
--
--   This identifies a divisorial correspondence on the degree-zero divisor class group of the base-changed modular function field with an endomorphism of the representing relative $\operatorname{Pic}^0$ scheme, once that endomorphism is known to classify the norm along $\pi_\alpha$ of the pullback along $\pi_\beta$ of the Poincaré bundle and to respect the group law. Specialised to $(M', \alpha, \beta)$ coming from level $N\ell$ it yields the Hecke operator as a morphism of $\mathbb{Q}$-schemes, and it is cited in the construction of the Hecke action on the relative Jacobian of the modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_pic0Correspondence_pts_eq_comp_of_poincare_pullbackAlong_iso.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_ArithmeticGalois
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

theorem ModularCurve.pic0Correspondence_pts_eq_comp_of_poincare_pullbackAlong_iso
    (N : ℕ) [NeZero N]
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ℚ)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℚ))) c)
    (D : RelativePic0Designation ℚ c)
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (aj : SchemeHomOver c D.toBase) (hajε : ε.1 ≫ aj.1 = D.zeroSection)
    (haj : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ)) (x : SchemeHomOver t c),
        Nonempty ((h.poincare.pullbackAlong
            ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩).L ≅
          (RelEffCartierDiv.ofPoint c x.1 x.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint c (t ≫ ε.1)
              ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t)))).idealModule))

    (Mη : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (eη : Mη.C ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))) [IsIso eη]
    (heη : eη ≫ pullback.snd c _ = Mη.toBase)
    (M' : ℕ) [NeZero M']

    (Y : Scheme.{0}) (cY : Y ⟶ Spec (CommRingCat.of ℚ))
    (πα πβ : Y ⟶ X) (hα : πα ≫ c = cY) (hβ : πβ ≫ c = cY)
    [IsFinite πα] [Flat πα] [LocallyOfFinitePresentation πα]
    [IsFinite πβ] [Flat πβ] [LocallyOfFinitePresentation πβ]
    (d : ℕ) (hdα : ∀ y, πα.finrank y = d)

    (φη : SchemeHomOver D.toBase D.toBase)
    (hφpt : ∀ z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))) D.toBase,
      Nonempty ((h.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp z φη)).L ≅
        Scheme.Modules.rigidify (rigSection c (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))) ε)
          (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))))
          (Scheme.Modules.normModule
            (curveChange πα hα (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))) d
            ((Scheme.Modules.pullback
              (curveChange πβ hβ (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))))).obj
              (h.poincare.pullbackAlong z).L))))
    (hφadd : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ℚ)) (x y : SchemeHomOver s D.toBase),
      NeronModelInfra.schemeHomOverComp
          ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul s x y) φη =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul s
          (NeronModelInfra.schemeHomOverComp x φη) (NeronModelInfra.schemeHomOverComp y φη))

    (Mη' : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar M'))
    (eη' : Mη'.C ⟶ pullback cY (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))) [IsIso eη']
    (heη' : eη' ≫ pullback.snd _ _ = Mη'.toBase)
    (α : modularFunctionFieldBar N →ₐ[AlgebraicClosure ℚ] modularFunctionFieldBar M') (hαI : α.toRingHom.IsIntegral)
    (β : modularFunctionFieldBar N →ₐ[AlgebraicClosure ℚ] modularFunctionFieldBar M') (hβI : β.toRingHom.IsIntegral)
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

    [hPD : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar M')]
    (hFI : FundamentalIdentityAlong (AlgebraicClosure ℚ) β hβI) (hfin : FiniteAlong (AlgebraicClosure ℚ) α)
    (hN : NormFormulaAlong (AlgebraicClosure ℚ) α hfin)

    (pts : JZero N ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))) D.toBase)
    (hadd : ∀ x y : JZero N,
      pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul _ (pts x) (pts y))
    (hnorm : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      s.1 ≫ eη ≫ pullback.fst c _ = Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) ≫ ε.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N),
        (Dv : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) =
          Finsupp.single (Mη.pointEquivPlace x) 1 - Finsupp.single (Mη.pointEquivPlace s) 1 ∧
        (pts (Pic0.mk Dv)).1 = x.1 ≫ eη ≫ pullback.fst c _ ≫ aj.1)
    (x : JZero N) :
    (pts (Pic0.correspondence β α hβI hαI hFI hfin hN x)).1 = (pts x).1 ≫ φη.1 := by sorry

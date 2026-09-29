-- Prove2me | Theorems.Thm_ModularCurve_heckeOperatorBar_points_eq_comp_of_transform_rat
-- name    : ModularCurve.heckeOperatorBar_points_eq_comp_of_transform_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/9a95c817-b333-569c-8d04-16840292a4eb
-- title:
--   Hecke operator T_q on J₀(p)(ℚ̄) realised by φ_η
-- statement:
--   Fix a nonzero natural number $p$ and a prime $q$ (with $pq \neq 0$). Let $c : X \to \operatorname{Spec}\mathbb{Q}$ be proper, smooth of relative dimension one and geometrically integral, and let $\varepsilon$ be a section of $c$. Let $D$ consist of a scheme with structure morphism `D.toBase` to $\operatorname{Spec}\mathbb{Q}$ and a zero section, and let `h` exhibit $D$ as representing the functor of $\varepsilon$-rigidified invertible modules on $X\times_{\mathbb Q}T$ whose restriction to every geometric fibre is algebraically equivalent to zero, with Poincaré bundle `h.poincare` and classifying maps `h.classify`; assume `D.toBase` smooth, proper and geometrically connected. Let $aj : X \to D$ be a morphism over $\mathbb{Q}$ with $\varepsilon$ followed by $aj$ the zero section, such that for every field $K$, every $t : \operatorname{Spec}K \to \operatorname{Spec}\mathbb{Q}$ and every $K$-point $x$ of $X$ over $t$, the pullback of the Poincaré bundle along $x$ followed by $aj$ has underlying module isomorphic to the line bundle of the relative Cartier divisor of $x$ tensored with the ideal module of the divisor $t \circ \varepsilon$, i.e. $\mathcal{O}(x)\otimes\mathcal{O}(-\varepsilon)$. Let `Mη` be a curve model over $\overline{\mathbb{Q}}$ of the field `modularFunctionFieldBar p` and `eη` an isomorphism of its curve with $X\times_{\mathbb Q}\overline{\mathbb Q}$ compatible with the structure morphisms, such that for $g \in \operatorname{Gal}(\overline{\mathbb Q}/\mathbb Q)$ and $\overline{\mathbb Q}$-points $x,x'$ with $x'$ the $g$-translate of $x$ in $X_{\overline{\mathbb Q}}$, the place attached to $x'$ is the `arithmeticGalois` image of $g$ applied to the place of $x$. Let $cY : Y \to \operatorname{Spec}\mathbb{Q}$ and let $\pi_\alpha, \pi_\beta : Y \to X$ be morphisms over $\mathbb{Q}$, both finite, flat and locally of finite presentation, with $\pi_\alpha$ of constant rank $d$. Let $\Phi$ be an operation on $\varepsilon$-rigidified line bundles over each base $t : T \to \operatorname{Spec}\mathbb{Q}$ whose underlying module is the re-rigidification along `rigSection` of the norm, relative to $\pi_\alpha\times T$ in rank $d$, of the pullback along $\pi_\beta\times T$; assume $\Phi$ preserves fibrewise algebraic triviality. Let $\varphi_\eta$ be an endomorphism of $D$ over $\mathbb{Q}$ such that the classifying map of $\Phi_t M$ is the classifying map of $M$ followed by $\varphi_\eta$, and such that post-composition with $\varphi_\eta$ is additive for the relative group law furnished by `h`. Let `Mη'` be a curve model over $\overline{\mathbb{Q}}$ of `modularFunctionFieldBar (p*q)` with an isomorphism `eη'` onto $Y\times_{\mathbb Q}\overline{\mathbb Q}$ over the base; assume the two degeneracy maps `heckeAlphaBar`, `heckeBetaBar` are integral, and that on $\overline{\mathbb{Q}}$-points $\pi_\alpha$ (respectively $\pi_\beta$) carries the place of a point of `Mη'.C` to its restriction along `heckeAlphaBar` (respectively `heckeBetaBar`). Finally let `pts` be a bijection from $\mathrm{Pic}^0$ of `modularFunctionFieldBar p` over $\overline{\mathbb Q}$ to the $\overline{\mathbb Q}$-points of $D$, additive for the relative group law, and such that for all $\overline{\mathbb Q}$-points $x$ and $s$ of `Mη.C` with $s$ the $\varepsilon$-point there is a degree-zero divisor equal to $[x]-[s]$ whose class is sent by `pts` to the point $x$ followed by $aj$. Then for every class $x$ in $\mathrm{Pic}^0$, the point `pts (heckeOperatorBar p q x)` is the point `pts x` followed by $\varphi_\eta$.
--
--   This is the statement that the Hecke operator $T_q$ on the degree-zero divisor class group of the modular function field of level $p$ over $\overline{\mathbb Q}$, transported to the $\overline{\mathbb Q}$-points of a relative $\mathrm{Pic}^0$ scheme $D$ over $\mathbb Q$ via the Abel–Jacobi pinning, is induced by the endomorphism $\varphi_\eta$ of $D$ classifying the norm-of-pullback operation along the degeneracy pair $(\pi_\alpha,\pi_\beta)$ over $\mathbb Q$. It feeds the construction of the Hecke action on the generic fibre of the relative $\mathrm{Pic}^0$ of the Deligne–Rapoport model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_heckeOperatorBar_points_eq_comp_of_transform_rat.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat
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
import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian ModularCurve AlgebraicCurve AlgebraicGeometry.SmoothProperCurve

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.heckeOperatorBar_points_eq_comp_of_transform_rat
    (p : ℕ) [NeZero p]
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ℚ)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℚ))) c)
    (D : RelativePic0Designation ℚ c)
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (hsm : Smooth D.toBase) (hpr : IsProper D.toBase) (hgc : GeometricallyConnected D.toBase)
    (aj : SchemeHomOver c D.toBase) (hajε : ε.1 ≫ aj.1 = D.zeroSection)
    (haj : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ)) (x : SchemeHomOver t c),
        Nonempty ((h.poincare.pullbackAlong
            ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩).L ≅
          (RelEffCartierDiv.ofPoint c x.1 x.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint c (t ≫ ε.1)
              ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t)))).idealModule))

    (Mη : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar p))
    (eη : Mη.C ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))) [IsIso eη]
    (heη : eη ≫ pullback.snd c _ = Mη.toBase)
    (hgal : ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (x x' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      x'.1 ≫ eη ≫ pullback.fst c _ =
        Spec.map (CommRingCat.ofHom (g : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
          x.1 ≫ eη ≫ pullback.fst c _ →
      Mη.pointEquivPlace x' =
        arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull p) g • Mη.pointEquivPlace x)
    (q : Nat.Primes) [NeZero (q : ℕ)] [NeZero (p * (q : ℕ))]

    (Y : Scheme.{0}) (cY : Y ⟶ Spec (CommRingCat.of ℚ))
    (πα πβ : Y ⟶ X) (hα : πα ≫ c = cY) (hβ : πβ ≫ c = cY)
    [IsFinite πα] [Flat πα] [LocallyOfFinitePresentation πα]
    [IsFinite πβ] [Flat πβ] [LocallyOfFinitePresentation πβ]
    (d : ℕ) (hdα : ∀ y, πα.finrank y = d)

    (Φ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℚ)),
      RigidifiedLineBundle c ε t → RigidifiedLineBundle c ε t)
    (hΦ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℚ)) (M : RigidifiedLineBundle c ε t),
      Nonempty ((Φ t M).L ≅ Scheme.Modules.rigidify (rigSection c t ε) (pullback.snd c t)
        (Scheme.Modules.normModule (curveChange πα hα t) d
          ((Scheme.Modules.pullback (curveChange πβ hβ t)).obj M.L))))
    (hcut : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℚ)) (M : RigidifiedLineBundle c ε t),
      (algEquivZeroCut c ε).P t M → (algEquivZeroCut c ε).P t (Φ t M))
    (φη : SchemeHomOver D.toBase D.toBase)
    (hφη : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℚ)) (M : RigidifiedLineBundle c ε t)
        (hM : (algEquivZeroCut c ε).P t M),
      postComp φη (h.classify t M hM) = h.classify t (Φ t M) (hcut t M hM))
    (hφadd : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ℚ)) (x y : SchemeHomOver s D.toBase),
      NeronModelInfra.schemeHomOverComp
          ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul s x y) φη =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul s
          (NeronModelInfra.schemeHomOverComp x φη) (NeronModelInfra.schemeHomOverComp y φη))

    (Mη' : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar (p * (q : ℕ))))
    (eη' : Mη'.C ⟶ pullback cY (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))) [IsIso eη']
    (heη' : eη' ≫ pullback.snd _ _ = Mη'.toBase)
    (hαI : (heckeAlphaBar (AlgebraicClosure ℚ) p q).toRingHom.IsIntegral)
    (hβI : (heckeBetaBar (AlgebraicClosure ℚ) p q).toRingHom.IsIntegral)
    (hplaceα : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη'.C // q ≫ Mη'.toBase = 𝟙 _})
        (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      y.1 ≫ eη' ≫ pullback.fst cY _ ≫ πα = x.1 ≫ eη ≫ pullback.fst c _ →
      Mη.pointEquivPlace x =
        Place.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) p q) hαI (Mη'.pointEquivPlace y))
    (hplaceβ : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη'.C // q ≫ Mη'.toBase = 𝟙 _})
        (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      y.1 ≫ eη' ≫ pullback.fst cY _ ≫ πβ = x.1 ≫ eη ≫ pullback.fst c _ →
      Mη.pointEquivPlace x =
        Place.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) p q) hβI (Mη'.pointEquivPlace y))

    (pts : JZero p ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))) D.toBase)
    (hadd : ∀ x y : JZero p,
      pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul _ (pts x) (pts y))
    (hnorm : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      s.1 ≫ eη ≫ pullback.fst c _ = Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) ≫ ε.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar p),
        (Dv : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar p)) =
          Finsupp.single (Mη.pointEquivPlace x) 1 - Finsupp.single (Mη.pointEquivPlace s) 1 ∧
        (pts (Pic0.mk Dv)).1 = x.1 ≫ eη ≫ pullback.fst c _ ≫ aj.1)
    (x : JZero p) :
    (pts (heckeOperatorBar p q x)).1 = (pts x).1 ≫ φη.1 := by sorry

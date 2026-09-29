-- Prove2me | Theorems.Thm_ModularCurve_exists_heckeEndomorphism_relJacobian_of_representsRelSubPic_of_ratCurveModel
-- name    : ModularCurve.exists_heckeEndomorphism_relJacobian_of_representsRelSubPic_of_ratCurveModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/417a08a2-7c05-5284-8656-53c9a8a679a6
-- title:
--   Hecke operator T_q as endomorphism of the relative Jacobian
-- statement:
--   Fix a natural number $p$ and a prime $\ell$ with $\ell \nmid p$, and write $R = \mathtt{ratLocalizedAt}\ \ell$ for the subring of $\mathbb{Q}$ of rationals whose denominator is coprime to $\ell$. Let $c : X \to \operatorname{Spec} R$ be proper, smooth of relative dimension $1$ and geometrically integral, with a section $\varepsilon$ of $c$, and let $D$ consist of a scheme $P$ with a structure morphism $P \to \operatorname{Spec} R$ and a zero section. The hypothesis $h$ asserts that $D$ represents, via a rigidified line bundle $\mathcal{P}$ on $X \times_R P$, the subfunctor of the $\varepsilon$-rigidified relative Picard functor of $c$ cut out by the condition that on every geometric fibre the bundle is algebraically equivalent to zero: for each $T \to \operatorname{Spec} R$ and each rigidified bundle $M$ on $X \times_R T$ satisfying this condition there is a unique $R$-morphism $T \to P$ pulling $\mathcal{P}$ back to $M$ up to isomorphism, and the pullback along the zero section is trivial. Assume $P \to \operatorname{Spec} R$ is smooth, proper and geometrically connected, and let $\mathrm{aj} : X \to P$ be an $R$-morphism with $\varepsilon$ followed by $\mathrm{aj}$ equal to the zero section, such that for every field $K$, every $K$-point $t$ of $\operatorname{Spec} R$ and every $t$-point $x$ of $X$ the pullback of $\mathcal{P}$ along $x$ followed by $\mathrm{aj}$ is isomorphic to the dual of the ideal sheaf of the graph of $x$, tensored with the ideal sheaf of the graph of $t$ followed by $\varepsilon$. Assume further: a curve model $M_\eta$ over $\overline{\mathbb{Q}}$ of the field $\mathtt{modularFunctionFieldBar}\ p$ (the base change to $\overline{\mathbb{Q}}$ inside $\overline{\mathbb{Q}}((q))$ of the modular function field of level $p$), an isomorphism $e_\eta$ of $M_\eta.C$ with $X \times_R \overline{\mathbb{Q}}$ over $\operatorname{Spec}\overline{\mathbb{Q}}$, and equivariance of the induced bijection between $\overline{\mathbb{Q}}$-points and places under $\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ acting through $\mathtt{arithmeticGalois}$; a curve model $M_0$ over $\mathbb{Q}$ of $\mathtt{modularFunctionFieldFull}\ p$ with an isomorphism $e_0$ of $M_0.C$ with $X \times_R \mathbb{Q}$, compatible with $M_\eta$ in the sense that the valuation ring of the place of a $\overline{\mathbb{Q}}$-point $x$ of $M_\eta.C$, intersected with the $\mathbb{Q}$-form via the base-change isomorphism, is the valuation ring of the place of the corresponding closed point of $M_0.C$. Then for every prime $q$ there is an $R$-endomorphism $\varphi$ of $P$ which is a homomorphism for the relative group law that $P$ carries by representing a group-valued functor (post-composition with $\varphi$ commutes with the group multiplication on $T$-points, for all $T \to \operatorname{Spec} R$), and which induces the Hecke operator $\mathtt{heckeOperatorBar}\ p\ q$: for every bijection $\mathrm{pts}$ from $\mathtt{JZero}\ p = \operatorname{Pic}^0(\overline{\mathbb{Q}}, \mathtt{modularFunctionFieldBar}\ p)$ to the $\overline{\mathbb{Q}}$-points of $P$ which is additive for that group law and normalised by Abel–Jacobi (for all $\overline{\mathbb{Q}}$-points $x, s$ of $M_\eta.C$ with $s$ corresponding to $\varepsilon$, the class of the degree-zero divisor $[\mathrm{place}(x)] - [\mathrm{place}(s)]$ is sent to $x$ followed by $e_\eta$, the first projection and $\mathrm{aj}$), one has $\mathrm{pts}(T_q x) = \mathrm{pts}(x)$ followed by $\varphi$ for all $x$.
--
--   This is the assertion that the Hecke correspondence $T_q$ acts on the relative Jacobian of $X_0(p)$ over $\mathbb{Z}_{(\ell)}$ by an endomorphism of the smooth proper group scheme, and not merely on its $\overline{\mathbb{Q}}$-points, the endomorphism being pinned down by its effect on degree-zero divisor classes of the geometric modular curve. It is the form proved with an explicit $\mathbb{Q}$-model of the generic fibre among the hypotheses, and is used in the assembly of the relative Jacobian of $X_0(p)$ together with its Hecke action.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_heckeEndomorphism_relJacobian_of_representsRelSubPic_of_ratCurveModel.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian ModularCurve AlgebraicCurve
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_heckeEndomorphism_relJacobian_of_representsRelSubPic_of_ratCurveModel
    (p : ℕ) [NeZero p] (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ¬ ℓ ∣ p)
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)))) c)
    (D : RelativePic0Designation ↥(GaloisRep.ratLocalizedAt ℓ) c)
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (hsm : Smooth D.toBase) (hpr : IsProper D.toBase) (hgc : GeometricallyConnected D.toBase)
    (aj : SchemeHomOver c D.toBase) (hajε : ε.1 ≫ aj.1 = D.zeroSection)
    (haj : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))) (x : SchemeHomOver t c),
        Nonempty ((h.poincare.pullbackAlong
            ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩).L ≅
          (RelEffCartierDiv.ofPoint c x.1 x.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint c (t ≫ ε.1)
              ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t)))).idealModule))

    (Mη : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar p))
    (eη : Mη.C ⟶ pullback c (Spec.map (CommRingCat.ofHom
      (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))))) [IsIso eη]
    (heη : eη ≫ pullback.snd c _ = Mη.toBase)
    (hgal : ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (x x' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      x'.1 ≫ eη ≫ pullback.fst c _ =
        Spec.map (CommRingCat.ofHom (g : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
          x.1 ≫ eη ≫ pullback.fst c _ →
      Mη.pointEquivPlace x' =
        arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull p) g • Mη.pointEquivPlace x)

    (M₀ : CurveModel ℚ ↥(modularFunctionFieldFull p))
    (e₀ : M₀.C ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ)))) [IsIso e₀]
    (he₀ : e₀ ≫ pullback.snd c _ = M₀.toBase)
    (hcompat : ∀ (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
        (y : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶
          pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ))))
        (x₀ : closedPoints M₀.C),
      y ≫ pullback.fst c _ = x.1 ≫ eη ≫ pullback.fst c _ →
      (y ≫ inv e₀).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) = x₀.1 →
      ((Mη.pointEquivPlace x).toValuationSubring.toSubring.comap
          ((baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull p)).toAlgHom.toRingHom.comp
            (Algebra.TensorProduct.includeRight (R := ℚ) (A := AlgebraicClosure ℚ)
              (B := ↥(modularFunctionFieldFull p))).toRingHom) =
        (M₀.placeOfPoint x₀).toValuationSubring.toSubring))
    (q : Nat.Primes) :
    ∃ φ : SchemeHomOver D.toBase D.toBase,
      (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)))
          (x y : SchemeHomOver s D.toBase),
        NeronModelInfra.schemeHomOverComp ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul s x y) φ =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul s (NeronModelInfra.schemeHomOverComp x φ)
            (NeronModelInfra.schemeHomOverComp y φ)) ∧
      ∀ (pts : JZero p ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom
          (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) D.toBase),
        (∀ x y : JZero p, pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul _ (pts x) (pts y)) →
        (∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
          s.1 ≫ eη ≫ pullback.fst c _ =
            Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))) ≫ ε.1 →
          ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar p),
            (Dv : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar p)) =
              Finsupp.single (Mη.pointEquivPlace x) 1 - Finsupp.single (Mη.pointEquivPlace s) 1 ∧
            (pts (Pic0.mk Dv)).1 = x.1 ≫ eη ≫ pullback.fst c _ ≫ aj.1) →
        ∀ x : JZero p, (pts (heckeOperatorBar p q x)).1 = (pts x).1 ≫ φ.1 := by sorry

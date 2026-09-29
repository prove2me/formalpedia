-- Prove2me | Theorems.Thm_ModularCurve_exists_pointsDict_pullback_snd_ratLocalizedAt_of_dRModelPackage_of_representsRelSubPic
-- name    : ModularCurve.exists_pointsDict_pullback_snd_ratLocalizedAt_of_dRModelPackage_of_representsRelSubPic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/592964a7-9cfc-5f01-9a15-1231eb510742
-- title:
--   Points dictionaries modulo ℓ for the relative Pic⁰ of X₀(p)
-- statement:
--   Fix a prime $p$ and a Deligne–Rapoport model package $\mathfrak X$ for level $p$ over $\mathbf Z$, with proper structure morphism `DRModel.toBase p`, and let $D$ consist of a $\mathbf Z$-scheme $D.P$ with structure morphism $D.toBase$ and a zero section. The hypotheses comprise: a datum `hD` exhibiting $D$ as representing the subfunctor of rigidified line bundles on the model, rigidified along $\mathfrak X.\varepsilon_\infty$, whose geometric fibres are algebraically equivalent to zero, together with smoothness and geometric connectedness of $D.toBase$; the analogous representability datum `h'` for the base change to $\mathbf Q$, a morphism $ajQ$ over $\mathbf Q$ from the base-changed curve to $D_{\mathbf Q}$, a morphism $aj$ from $\mathfrak X.M_\eta.C$ to $D.P$ and a $\bar{\mathbf Q}$-point $\bar\varepsilon$ of $\mathfrak X.M_\eta.C$; a bijection $\mathrm{pts}$ from the degree-zero divisor class group of the modular function field over $\bar{\mathbf Q}$ onto the $\bar{\mathbf Q}$-points of $D$, additive for the group law supplied by `hD` and equivariant for $\mathrm{Gal}(\bar{\mathbf Q}/\mathbf Q)$ acting through $\mathrm{Spec}$ of $\sigma$; properness of the base change of $D.toBase$ to $\mathbf Z[1/p]$; an isomorphism between the Poincaré bundle of `h'` and the base change along $\mathbf Q$ of that of `hD`; the normalisations $\varepsilon_\infty\circ ajQ =$ zero section and $aj\circ\bar\varepsilon =$ zero section, compatibility of $aj$ over $\bar{\mathbf Q}$, of $\bar\varepsilon$ with $\varepsilon_\infty$, and a factorisation of $aj$ through $\mathfrak X.e_\eta$, a comparison morphism $k_0$ and $ajQ$; the Abel–Jacobi identity for $ajQ$, stating for every field $K$, every $K$-point $t$ of $\mathrm{Spec}\,\mathbf Q$ and every $x$ over $t$ that the pullback of the Poincaré bundle along $x\circ ajQ$ is isomorphic to the line bundle of the relative effective Cartier divisor of $x$ tensored with the ideal module of the divisor of $t\circ\varepsilon_\infty$; and the statement that for each $\bar{\mathbf Q}$-point $x$ the class of $(x)-(\bar\varepsilon)$, formed from the places attached to $x$ and $\bar\varepsilon$ by $\mathfrak X.M_\eta$, corresponds under $\mathrm{pts}$ to $x\circ aj$. Let further $\ell$ be a prime with $\ell\nmid p$, write $R$ for the subring [`GaloisRep.ratLocalizedAt ℓ`](def/GaloisRep_Flat.html#L8) of $\mathbf Q$ of rationals whose denominator is coprime to $\ell$, and let $D_R$ be the base change of $D.toBase$ to $R$; assume $D_R$ is smooth, proper, with connected fibres and carrying a relative group law, let $L'$ be a relative group law on $D_R$ whose multiplication is compatible along the first projection with the group law of `hD`, and let $\mathrm{pts}'$ be a bijection from the same divisor class group onto the $\bar{\mathbf Q}$-points of $D_R$ over $R$ lifting $\mathrm{pts}$ along the first projection. Then for every valuation subring $A'$ of $\bar{\mathbf Q}$ with $\ell$ a non-unit of $A'$ there exist a morphism $\sigma_{A'}\colon \mathrm{Spec}\,A'\to\mathrm{Spec}\,R$, a bijection $\mathrm{pts}_{A'}$ from the divisor class group onto the points of $D_R$ over $\mathrm{Spec}\,A'\to\mathrm{Spec}\,R$ read through $A'\hookrightarrow\bar{\mathbf Q}$, and a bijection $\mathrm{pts}_{\mathrm{sp}}$ from the degree-zero divisor class group of the corresponding function field over the residue field of $A'$ onto the points of $D_R$ over the residue point, such that $\mathrm{pts}_{A'}$ has the same underlying morphisms as $\mathrm{pts}'$, $\mathrm{pts}_{\mathrm{sp}}$ is additive for $L'$, and, provided the reduction inputs `ReductionInputsModL A' p` hold, the predicate `ReductionOfPointsAgreesModL` holds: every class $x$ lifts to an $A'$-point of $D_R$ over $\sigma_{A'}$ whose restriction to $\bar{\mathbf Q}$ is $\mathrm{pts}_{A'}(x)$ and whose reduction is $\mathrm{pts}_{\mathrm{sp}}$ of the reduction of $x$ modulo $\ell$.
--
--   This is the points-dictionary part of the good-reduction data for $J_0(p)$ at a prime $\ell$ not dividing $p$: it transports the divisor-class description of $J_0(p)(\bar{\mathbf Q})$ to the $\mathbf Z_{(\ell)}$-model of the relative $\mathrm{Pic}^0$ and matches reduction of points with reduction of divisor classes. It is used in the construction of the good-prime datum and of the Néron identity component of $J_0(p)$ at $\ell$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_pointsDict_pullback_snd_ratLocalizedAt_of_dRModelPackage_of_representsRelSubPic.lean

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
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_ModularCurve_ReductionOfPointsAgreesModL
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_ModularCurve_HeckeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  ModularCurve AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve IsLocalRing

set_option maxHeartbeats 800000 in

theorem ModularCurve.exists_pointsDict_pullback_snd_ratLocalizedAt_of_dRModelPackage_of_representsRelSubPic
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) [IsProper (DRModel.toBase p)]
    (D : RelativePic0Designation ℤ (DRModel.toBase p))
    (hD : RepresentsRelSubPic (DRModel.toBase p) 𝔛.εinf (algEquivZeroCut (DRModel.toBase p) 𝔛.εinf) D)
    (hsm : Smooth D.toBase) (hconn : GeometricallyConnected D.toBase)

    (h' : RepresentsRelSubPic (baseChange ℤ (DRModel.toBase p) ℚ) (sectionBaseChange ℚ 𝔛.εinf)
      (algEquivZeroCut (baseChange ℤ (DRModel.toBase p) ℚ) (sectionBaseChange ℚ 𝔛.εinf)) (D.baseChange ℚ))
    (ajQ : SchemeHomOver (baseChange ℤ (DRModel.toBase p) ℚ) (D.baseChange ℚ).toBase)
    (aj : 𝔛.Mη.C ⟶ D.P)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Mη.C // q ≫ 𝔛.Mη.toBase = 𝟙 _})
    (pts : JZero p ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) D.toBase)
    (pts_add : ∀ x y : JZero p, pts (x + y) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf) hD).mul _ (pts x) (pts y))
    (pts_galois : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JZero p),
      (pts (σ • x)).1 = Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts x).1)
    (proper_away : IsProper (pullback.snd D.toBase
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ (Localization.Away (p : ℤ)))))))
    (hP : Nonempty (h'.poincare.L ≅ (BaseChange.ofR (DRModel.toBase p) 𝔛.εinf ℚ
      (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap ℤ ℚ), pullback.condition⟩)).L))
    (hajε : (sectionBaseChange ℚ 𝔛.εinf).1 ≫ ajQ.1 = (D.baseChange ℚ).zeroSection)
    (haj : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
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
    (hεbar : εbar.1 ≫ 𝔛.eη ≫ pullback.fst (DRModel.toBase p) _ =
        Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))) ≫ 𝔛.εinf.1)
    (hεbar_aj : εbar.1 ≫ aj = Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))) ≫ D.zeroSection)
    (hpts_aj : ∀ x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Mη.C // q ≫ 𝔛.Mη.toBase = 𝟙 _},
        ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar p)),
          (Dv : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p)) =
            Finsupp.single (𝔛.Mη.pointEquivPlace x) 1 - Finsupp.single (𝔛.Mη.pointEquivPlace εbar) 1 ∧
          (pts (Pic0.mk Dv)).1 = x.1 ≫ aj)

    (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ¬ ℓ ∣ p)
    (hbundle : AbelianSchemePropertyBundle ↥(GaloisRep.ratLocalizedAt ℓ) (pullback.snd D.toBase (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ))))))
    (L' : RelativeGroupLaw ↥(GaloisRep.ratLocalizedAt ℓ) (pullback.snd D.toBase (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ))))))
    (hL' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)))
      (x y : SchemeHomOver t (pullback.snd D.toBase (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ))))))
      (X Y : SchemeHomOver (t ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ)))) D.toBase),
      X.1 = x.1 ≫ pullback.fst _ _ → Y.1 = y.1 ≫ pullback.fst _ _ →
      (L'.mul t x y).1 ≫ pullback.fst _ _ = ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf) hD).mul _ X Y).1)
    (pts' : JZero p ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom
      (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) (pullback.snd D.toBase (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ))))))
    (hpts' : ∀ x : JZero p, (pts' x).1 ≫ pullback.fst _ _ = (pts x).1) :
    ∀ (A' : ValuationSubring (AlgebraicClosure ℚ)), A'.LiesOverPrime ℓ →
      ∃ (σA : Spec (CommRingCat.of ↥A') ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)))
        (ptsA : JZero p ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom A'.subtype) ≫ σA) (pullback.snd D.toBase (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ))))))
        (ptsSp : JZeroC (ResidueField ↥A') p ≃
          SchemeHomOver (Spec.map (CommRingCat.ofHom (residue ↥A')) ≫ σA) (pullback.snd D.toBase (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ)))))),
        (∀ x : JZero p, (ptsA x).1 = (pts' x).1) ∧
        (∀ u v : JZeroC (ResidueField ↥A') p, ptsSp (u + v) = L'.mul _ (ptsSp u) (ptsSp v)) ∧
        (ReductionInputsModL A' p → ReductionOfPointsAgreesModL p A' (pullback.snd D.toBase (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ))))) σA ptsA ptsSp) := by sorry

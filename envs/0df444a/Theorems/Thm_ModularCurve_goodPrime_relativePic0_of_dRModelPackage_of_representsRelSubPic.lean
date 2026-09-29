-- Prove2me | Theorems.Thm_ModularCurve_goodPrime_relativePic0_of_dRModelPackage_of_representsRelSubPic
-- name    : ModularCurve.goodPrime_relativePic0_of_dRModelPackage_of_representsRelSubPic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/838baef6-f5d4-5a8f-9da1-ced13a58e855
-- title:
--   Good-prime data for relative Pic⁰ of the DR model at ℓ ∤ p
-- statement:
--   Let $p$ be a prime, let $\mathfrak X$ be a `DRModelPackage` for $p$ (a bundle of data on the two-chart integral model `DRModel p` of the modular function field of level $p$, including the curve models $M_0$ over $\mathbf Q$ and $M_\eta$ over $\overline{\mathbf Q}$, the sections $\varepsilon_\infty,\varepsilon_0$ and the smooth locus), let $I$ be `LegTwoInput` data for $\mathfrak X$, and assume `DRModel.toBase p` is proper. Let $D$ consist of a scheme $D.P$ over $\operatorname{Spec}\mathbf Z$ with a zero section, and let $hD$ exhibit $D$ as representing the subfunctor of rigidified relative line bundles on the model that are fibrewise algebraically equivalent to zero (a Poincaré bundle in this class, the universal property, and triviality along the zero section), with $D.\mathrm{toBase}$ smooth and geometrically connected. Further hypotheses are assumed, summarised here in groups: the analogous representability $h'$ after base change to $\mathbf Q$ together with the comparison $hP$ of Poincaré bundles; an Abel–Jacobi morphism $ajQ$ over $\mathbf Q$ and a morphism $aj$ from $M_\eta.C$ to $D.P$ with their normalisations at $\varepsilon_\infty$, $\bar\varepsilon$ and the divisor-class identification $haj$, $hk_0$, $h\varepsilon$, $hpts\_aj$ (the class of $[x]-[\bar\varepsilon]$ corresponds to $x$ composed with $aj$); a bijection $pts$ from $J_0(p) = \mathrm{Pic}^0$ of the geometric modular function field onto the $\overline{\mathbf Q}$-points of $D.\mathrm{toBase}$, additive for the relative group law attached to $hD$ and Galois-equivariant; properness of $D.\mathrm{toBase}$ after base change to $\mathbf Z[1/p]$; and a Hecke field assigning to each $t$ in `HeckeAlg` an endomorphism of $D.\mathrm{toBase}$ over $\operatorname{Spec}\mathbf Z$ which is a homomorphism for the relative group law and induces the action of $t$ on $pts$. The conclusion is that for every prime $\ell$ with $\ell \nmid p$ the type `JZeroNeronIdentityComponent.GoodPrimeData p D.toBase L pts ℓ` is inhabited, where $L$ is the relative group law from $hD$: that is, the base change of $D.\mathrm{toBase}$ to $\mathbf Z_{(\ell)}$ carries a relative group law and a $\overline{\mathbf Q}$-points dictionary compatible with $L$ and $pts$, is commutative, additive and Galois-equivariant, carries an abelian-scheme property bundle, admits at each valuation ring of $\overline{\mathbf Q}$ above $\ell$ integral and special-fibre point dictionaries whose reductions agree, and carries the Hecke action by homomorphic endomorphisms.
--
--   This packages the good-reduction input at a prime $\ell$ different from $p$: the relative $\mathrm{Pic}^0$ of the Deligne–Rapoport model of $X_0(p)$, base changed to $\mathbf Z_{(\ell)}$, is an abelian scheme with Hecke action and a reduction dictionary for divisor classes. It feeds [`ModularCurve.nonempty_jZeroNeronIdentityComponentGood_of_dRModelPackage_of_ffPin`](thm.html#ModularCurve.nonempty_jZeroNeronIdentityComponentGood_of_dRModelPackage_of_ffPin), and thence the $\ell$-adic Galois representations attached to $J_0(p)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_goodPrime_relativePic0_of_dRModelPackage_of_representsRelSubPic.lean

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
import Definitions.Def_ModularCurve_JZeroNeronIdentityComponentGood

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  ModularCurve AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve IsLocalRing

theorem ModularCurve.goodPrime_relativePic0_of_dRModelPackage_of_representsRelSubPic
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (I : 𝔛.LegTwoInput) [IsProper (DRModel.toBase p)]
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

    (hecke : letI := heckeModuleBar p
      ∀ t : HeckeAlg, ∃ φ : SchemeHomOver D.toBase D.toBase,
        (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ℤ)) (x y : SchemeHomOver s D.toBase),
          (⟨((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf) hD).mul s x y).1 ≫ φ.1,
            by rw [Category.assoc, φ.2]; exact ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf) hD).mul s x y).2⟩ : SchemeHomOver s D.toBase) =
            (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf) hD).mul s
              ⟨x.1 ≫ φ.1, by rw [Category.assoc, φ.2]; exact x.2⟩ ⟨y.1 ≫ φ.1, by rw [Category.assoc, φ.2]; exact y.2⟩) ∧
        ∀ x : JZero p, (pts (t • x)).1 = (pts x).1 ≫ φ.1) :
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ ℓ ∣ p →
      Nonempty (JZeroNeronIdentityComponent.GoodPrimeData p D.toBase
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf) hD) pts ℓ) := by sorry

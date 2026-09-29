-- Prove2me | Theorems.Thm_ModularCurve_DRResolvedModelPackage_eEta_comp_pullbackMap_eq_comp_toDR_of_comp_fst_eq
-- name    : ModularCurve.DRResolvedModelPackage.eEta_comp_pullbackMap_eq_comp_toDR_of_comp_fst_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:14.444979+00:00
-- url     : https://prove2.me/theorems/5583a100-e2b9-5006-9a63-33b8fbc997af
-- title:
--   Base change along τ of a section and its geometric generic point
-- statement:
--   Fix a prime $p$ and a package $\mathfrak{X}$ of type `DRModelPackage p`, which carries the two-chart integral model `DRModel p` of the full modular function field over $\operatorname{Spec}\mathbb{Z}$ together with its generic models, in particular a curve model $\mathfrak{X}.M\eta$ over $\overline{\mathbb{Q}}$ and an isomorphism $\mathfrak{X}.e\eta$ from $\mathfrak{X}.M\eta.C$ onto the base change of `DRModel p` to $\operatorname{Spec}\overline{\mathbb{Q}}$ satisfying $e\eta \circ$ second projection $=M\eta.\mathrm{toBase}$. Let $O$ be a commutative ring, $\kappa$ an algebraically closed field of characteristic $p$, $\mathrm{to}\kappa : O \to \kappa$ a ring homomorphism, and $\mathfrak{X}_{\mathrm{reg}}$ a resolved model package of type `DRResolvedModelPackage p 𝔛 O κ toκ`, with underlying scheme $Y$, structure morphism $\mathrm{toBase}: Y \to \operatorname{Spec} O$ and proper morphism $\mathrm{toDR}: Y \to \mathrm{DRModel}(p) \times_{\mathbb{Z}} \operatorname{Spec} O$ satisfying $\mathrm{toDR}$ followed by the second projection $=\mathrm{toBase}$. Let $\tau : O \to \overline{\mathbb{Q}}$ be a ring homomorphism, let $t : \operatorname{Spec} O \to Y$ be a section of $\mathrm{toBase}$ (that is, $t$ followed by $\mathrm{toBase}$ is the identity), and let $q$ be a $\overline{\mathbb{Q}}$-point of $\mathfrak{X}.M\eta.C$, i.e. $q$ followed by $M\eta.\mathrm{toBase}$ is the identity of $\operatorname{Spec}\overline{\mathbb{Q}}$. Assume that $\operatorname{Spec}\tau$, then $t$, then $\mathrm{toDR}$, then the projection to $\mathrm{DRModel}(p)$ agrees with $q$, then $e\eta$, then the projection to $\mathrm{DRModel}(p)$. The conclusion is that $q$ followed by $e\eta$ followed by the canonical morphism $\mathrm{DRModel}(p)\times_{\mathbb{Z}}\operatorname{Spec}\overline{\mathbb{Q}} \to \mathrm{DRModel}(p)\times_{\mathbb{Z}}\operatorname{Spec} O$ induced by the identity on $\mathrm{DRModel}(p)$, by $\operatorname{Spec}\tau$ on the base factor and by the identity on $\operatorname{Spec}\mathbb{Z}$, equals $\operatorname{Spec}\tau$ followed by $t$ followed by $\mathrm{toDR}$.
--
--   This is a bookkeeping identity translating between two ways of saying that the geometric generic point of an $O$-section of a resolved model is the given $\overline{\mathbb{Q}}$-point $q$ of the generic curve model: the form in which the statement arises from the model package and the form in which it is consumed when comparing Picard data along the resolution. It is used in the construction of sections of the resolved model from degree-zero divisor classes killed by the Abel–Jacobi type map, namely by [`ModularCurve.DRModelPackage.exists_schemeHomOver_of_comp_eq_zero_of_abelJacobiPin_of_surjective`](thm.html#ModularCurve.DRModelPackage.exists_schemeHomOver_of_comp_eq_zero_of_abelJacobiPin_of_surjective).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRResolvedModelPackage_eEta_comp_pullbackMap_eq_comp_toDR_of_comp_fst_eq.lean

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
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  ModularCurve AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve
open IsLocalRing ModularCurve.PlaceSpecialization

set_option maxHeartbeats 800000 in

theorem ModularCurve.DRResolvedModelPackage.eEta_comp_pullbackMap_eq_comp_toDR_of_comp_fst_eq
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p)
    (O : Type) [CommRing O] [IsDomain O]
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ)
    (𝔛reg : DRResolvedModelPackage p 𝔛 O κ toκ)
    (τ : O →+* AlgebraicClosure ℚ)
    (t : SchemeHomOver (𝟙 (Spec (CommRingCat.of O))) 𝔛reg.toBase)
    (q : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Mη.C // q ≫ 𝔛.Mη.toBase = 𝟙 _})
    (h : Spec.map (CommRingCat.ofHom τ) ≫ t.1 ≫ 𝔛reg.toDR ≫
          pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) =
        q.1 ≫ 𝔛.eη ≫ pullback.fst (DRModel.toBase p) _) :
    q.1 ≫ 𝔛.eη ≫
        pullback.map (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))
          (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) (𝟙 _) (Spec.map (CommRingCat.ofHom τ)) (𝟙 _)
          (by simp)
          (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp]; congr 2; exact RingHom.ext_int _ _) =
      Spec.map (CommRingCat.ofHom τ) ≫ t.1 ≫ 𝔛reg.toDR := by sorry

-- Prove2me | Theorems.Thm_ModularCurve_DRResolvedModelPackage_exists_section_toDR_generic_eq_pointEquivPlace_symm_of_forall_inertia_smul_eq
-- name    : ModularCurve.DRResolvedModelPackage.exists_section_toDR_generic_eq_pointEquivPlace_symm_of_forall_inertia_smul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:14.444979+00:00
-- url     : https://prove2.me/theorems/a8aa619a-6734-59d4-982c-cca76b718f60
-- title:
--   Inertia-fixed places give sections of the resolved model
-- statement:
--   Fix a prime $p$, a package $\mathfrak{X}$ of Deligne–Rapoport model data at level $p$, and a valuation subring $A$ of $\overline{\mathbb{Q}}$ with $p$ a nonunit of $A$ (the hypothesis `hA`). Let $O$ be a discrete valuation domain together with a ring isomorphism $eO$ onto the pullback of $A$ along the inclusion of the fixed field of `A.inertiaSubgroupIn ℚ` (the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ inside its decomposition subgroup) into $\overline{\mathbb{Q}}$; let $\kappa$ be an algebraically closed field of characteristic $p$ with a ring map $\mathrm{to}\kappa : O \to \kappa$, and let $\mathfrak{X}reg$ be a `DRResolvedModelPackage` for $p$, $\mathfrak{X}$, $O$, $\kappa$, $\mathrm{to}\kappa$: an integral, locally Noetherian scheme $Y$, proper and flat over $\mathrm{Spec}\,O$, regular of stalk Krull dimension at most $2$ away from the $p$-invertible locus, with a proper morphism `toDR` to the base change of the Deligne–Rapoport model to $O$ which is an isomorphism over the smooth locus and over the generic fibre, plus the nodal-component data. Let $ePl$ be a bijection from places of $\overline{\mathbb{Q}}$-rational modular function field at level $1\cdot p$ to those at level $p$, equivariant for the arithmetic Galois actions (`hePl_gal`), and let $V$ be a place at level $1\cdot p$ fixed by the arithmetic Galois action of every element of `A.inertiaSubgroupIn ℚ`. Then there is a section $t$ of $\mathfrak{X}reg.\mathrm{toBase}$ over $\mathrm{Spec}\,O$, i.e. a morphism $\mathrm{Spec}\,O \to Y$ composing with `toBase` to the identity, whose generic point agrees with $V$: precomposing $t$ with the morphism $\mathrm{Spec}\,\overline{\mathbb{Q}} \to \mathrm{Spec}\,O$ induced by $O \cong A \cap \overline{\mathbb{Q}}^{I} \hookrightarrow \overline{\mathbb{Q}}$ and then with `toDR` followed by the first projection to `DRModel p` gives the same $\overline{\mathbb{Q}}$-point of `DRModel p` as the point of $\mathfrak{X}.M\eta.C$ corresponding to the place $ePl\,V$ under $\mathfrak{X}.M\eta.\mathrm{pointEquivPlace}$, followed by $\mathfrak{X}.e\eta$ and the first projection.
--
--   This is the extension step for points: a place of the modular function field over $\overline{\mathbb{Q}}$ which is fixed by inertia at a place above $p$ descends to the valuation ring of the inertia field and, by properness and regularity of the resolved Deligne–Rapoport model, spreads out to a section over that discrete valuation ring with the prescribed generic point. It feeds the construction of sections used to compute multidegrees and depths of components in the resolved model, and is cited by [`ModularCurve.DRModelPackage.exists_schemeHomOver_of_comp_eq_zero_of_abelJacobiPin_of_surjective`](thm.html#ModularCurve.DRModelPackage.exists_schemeHomOver_of_comp_eq_zero_of_abelJacobiPin_of_surjective) and [`ModularCurve.DRResolvedModelPackage.exists_isStrictFst_forall_inertia_smul_eq_and_section_toDR_generic_eq`](thm.html#ModularCurve.DRResolvedModelPackage.exists_isStrictFst_forall_inertia_smul_eq_and_section_toDR_generic_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRResolvedModelPackage_exists_section_toDR_generic_eq_pointEquivPlace_symm_of_forall_inertia_smul_eq.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  ModularCurve AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve
open IsLocalRing ModularCurve.PlaceSpecialization

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.DRResolvedModelPackage.exists_section_toDR_generic_eq_pointEquivPlace_symm_of_forall_inertia_smul_eq
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p)
    {A : ValuationSubring (AlgebraicClosure ℚ)} (hA : A.LiesOverPrime p)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (eO : O ≃+* ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))))
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ)
    (𝔛reg : DRResolvedModelPackage p 𝔛 O κ toκ)
    (ePl : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ≃ Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p))
    (hePl_gal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))),
      ePl (arithmeticGalois (modularFunctionFieldFull (1 * p)) σ • V) = arithmeticGalois (modularFunctionFieldFull p) σ • ePl V)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)))
    (hV : ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * p)) σ • V = V) :
    ∃ t : SchemeHomOver (𝟙 (Spec (CommRingCat.of O))) 𝔛reg.toBase,
      Spec.map (CommRingCat.ofHom ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
            (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom)))) ≫ t.1 ≫ 𝔛reg.toDR ≫
          pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) =
        ((𝔛.Mη.pointEquivPlace).symm (ePl V)).1 ≫ 𝔛.eη ≫ pullback.fst (DRModel.toBase p) _ := by sorry

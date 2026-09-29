-- Prove2me | Theorems.Thm_ModularCurve_DRResolvedModelPackage_exists_isStrictFst_forall_inertia_smul_eq_and_section_toDR_generic_eq
-- name    : ModularCurve.DRResolvedModelPackage.exists_isStrictFst_forall_inertia_smul_eq_and_section_toDR_generic_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:14.444979+00:00
-- url     : https://prove2.me/theorems/40830a03-c76f-596d-b764-f780aefcf4bd
-- title:
--   Inertia-fixed strict place with an 𝒪-section of the resolved model
-- statement:
--   Fix a prime $p$, a Deligne–Rapoport model package $\mathfrak X$ for $p$, and a valuation subring $A$ of $\overline{\mathbf Q}$ with $p$ a non-unit of $A$. Let $\mathcal O$ be a discrete valuation domain together with a ring isomorphism $e_{\mathcal O}$ onto the contraction of $A$ to the fixed field of the inertia subgroup $I_A =$ `A.inertiaSubgroupIn ℚ`, let $\kappa$ be an algebraically closed field of characteristic $p$ with a ring homomorphism $\mathcal O \to \kappa$, and let $\mathfrak X^{\mathrm{reg}}$ be a resolved model package for $\mathfrak X$ over $(\mathcal O,\kappa)$. Let $e_{\mathrm{Pl}}$ be a bijection between the places of $\overline{\mathbf Q}$-level $1\cdot p$ and of level $p$ modular function fields commuting with the arithmetic Galois actions. Let $k$ be an algebraically closed field of characteristic $p$, $\mathrm{red} : A \to k$ a ring homomorphism, `data` a modular polynomial datum for $p$ satisfying the Kronecker congruence, with the Hecke maps $\bar\alpha, \bar\beta$ at level $(1,p)$ integral, and let $P$ be a place specialisation of type `PlaceSpecialization A p 1 data hKr k red hα hβ`. Then there is a place $V$ of `modularFunctionFieldBar (1 * p)` over $\overline{\mathbf Q}$ such that: $V$ is fixed by the arithmetic-Galois action of every $\sigma \in I_A$; $P$ is strict of the first kind at $V$, i.e. the geometric-level Frobenius `frobOnPlacesGeomLevel` carries $P.\mathrm{reduceFst}\,V$ (the specialisation under $P.\mathrm{sp}$ of the restriction of $V$ along $\bar\alpha$) to $P.\mathrm{reduceSnd}\,V$ (the same for $\bar\beta$), while its square does not fix $P.\mathrm{reduceFst}\,V$; and there is a section $t$ of $\mathfrak X^{\mathrm{reg}}$ over $\operatorname{Spec}\mathcal O$, i.e. $t : \operatorname{Spec}\mathcal O \to \mathfrak X^{\mathrm{reg}}.Y$ with $t$ followed by the structure morphism the identity, whose base change along $\mathcal O \to \overline{\mathbf Q}$ (through $e_{\mathcal O}$, the contracted valuation ring and the fixed field) and push to the Deligne–Rapoport model $\mathfrak X$ coincides with the $\overline{\mathbf Q}$-point of $\mathfrak X$ attached by $\mathfrak X.M_\eta.\mathrm{pointEquivPlace}^{-1}$ to $e_{\mathrm{Pl}}(V)$ and the isomorphism $\mathfrak X.e_\eta$ of the generic fibre.
--
--   This supplies the orientation datum used in the Deligne–Rapoport-model analysis of supersingular points: an inertia-invariant place of $X_0(p)$ at which the Kronecker correspondence is strict of the first kind, realised by an $\mathcal O$-valued section of the resolved model passing through the corresponding geometric point. It is the inhabitation statement feeding the branch/depth computation [`ModularCurve.DRModelPackage.exists_germ_jq_sub_pow_and_stalkSpecializes_mem_maximalIdeal_of_swap`](thm.html#ModularCurve.DRModelPackage.exists_germ_jq_sub_pow_and_stalkSpecializes_mem_maximalIdeal_of_swap).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRResolvedModelPackage_exists_isStrictFst_forall_inertia_smul_eq_and_section_toDR_generic_eq.lean

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
import Definitions.Def_ModularCurve_GlueData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  ModularCurve AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve
open IsLocalRing
open ModularCurve.PlaceSpecialization
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.DRResolvedModelPackage.exists_isStrictFst_forall_inertia_smul_eq_and_section_toDR_generic_eq
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p)
    {A : ValuationSubring (AlgebraicClosure ℚ)} (hA : A.LiesOverPrime p)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (eO : O ≃+* ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))))
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ)
    (𝔛reg : DRResolvedModelPackage p 𝔛 O κ toκ)
    (ePl : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ≃ Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p))
    (hePl_gal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))),
      ePl (arithmeticGalois (modularFunctionFieldFull (1 * p)) σ • V) = arithmeticGalois (modularFunctionFieldFull p) σ • ePl V)

    {k : Type} [Field k] [CharP k p] [IsAlgClosed k] [DecidableEq k] {red : ↥A →+* k}
    {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 p} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 p}
    (P : PlaceSpecialization A p 1 data hKr k red hα hβ) :
    ∃ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)),
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * p)) σ • V = V) ∧
      P.IsStrictFst V ∧
      ∃ t : SchemeHomOver (𝟙 (Spec (CommRingCat.of O))) 𝔛reg.toBase,
        Spec.map (CommRingCat.ofHom ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
              (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom)))) ≫ t.1 ≫ 𝔛reg.toDR ≫
            pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) =
          ((𝔛.Mη.pointEquivPlace).symm (ePl V)).1 ≫ 𝔛.eη ≫ pullback.fst (DRModel.toBase p) _ := by sorry

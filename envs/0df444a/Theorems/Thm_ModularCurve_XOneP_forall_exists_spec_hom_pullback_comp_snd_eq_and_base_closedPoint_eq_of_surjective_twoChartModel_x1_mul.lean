-- Prove2me | Theorems.Thm_ModularCurve_XOneP_forall_exists_spec_hom_pullback_comp_snd_eq_and_base_closedPoint_eq_of_surjective_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.forall_exists_spec_hom_pullback_comp_snd_eq_and_base_closedPoint_eq_of_surjective_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/9f8b956f-1802-5f26-beb0-9a4ba265d52d
-- title:
--   Crossings of the two-chart model as residue-field points
-- statement:
--   Fix a prime $p$ and $M$ with $5 \le M$ and $p \nmid M$; let $L$ be a characteristic-zero field that is a cyclotomic extension of $\mathbb{Q}$ for $\{p\}$, and $\zeta \in L$ a primitive $p$-th root of unity. Let $K$ be the intermediate field of $L \subseteq \mathrm{LaurentSeries}\,L$ obtained by adjoining to $L$ the coefficientwise image under $\mathbb{Q} \to L$ of the $q$-expansion function field [`ModularCurve.x1FunctionField (M * p)`](def/ModularCurve_X1.html#L137) of level $\Gamma_1(Mp)$. Let $A$ be a discrete valuation domain with fraction field $L$, with $p$ in its maximal ideal, with $\zeta$ in the image of $A$, and acting on $K$ compatibly, and let $j \in K$ be nonzero with Laurent expansion the coefficientwise image of [`ModularCurve.jq`](def/ModularCurve_X0.html#L157). Write $X = \mathrm{TwoChartModel}\,A\,K\,j$, the pushout of the two charts $\operatorname{Spec} A[j]$, $\operatorname{Spec} A[j^{-1}]$, with structure morphism [`ModularCurve.TwoChart.modelTo`](def/ModularCurve_TwoChartModel.html#L252) to $\operatorname{Spec} A$. Let $k$ be an algebraically closed $A$-algebra field of characteristic $p$, and let $c_1 : C_1 \to \operatorname{Spec} k$, $c_2 : C_2 \to \operatorname{Spec} k$ be proper, smooth of relative dimension $1$ and geometrically integral. Let $i_1, i_2$ be closed immersions of $C_1, C_2$ into the fibre product $X \times_{\operatorname{Spec} A} \operatorname{Spec} k$ commuting with the projection to $\operatorname{Spec} k$, whose images together cover every point of that fibre product, and assume the scheme $C_1 \times_{X_k} C_2$ is reduced with $\mathrm{Nat.card} = n > 0$. Let $O$ be a discrete valuation domain, $\rho_O : A \to O$ and $\mathrm{to}\kappa : O \to k$ ring homomorphisms with $\mathrm{to}\kappa \circ \rho_O$ the structure map $A \to k$ and $\mathrm{to}\kappa$ surjective, and let $bc : X \times_A \operatorname{Spec} k \to X \times_A \operatorname{Spec} O$ commute with the first projections and satisfy $bc$ followed by the second projection $=$ the second projection followed by $\operatorname{Spec}(\mathrm{to}\kappa)$. Then for every point $x$ of $C_1 \times_{X_k} C_2$ there is a morphism $s : \operatorname{Spec}$ of the residue field of $O$ to $X \times_A \operatorname{Spec} O$ such that $s$ followed by the second projection is $\operatorname{Spec}$ of the residue map $O \to O/\mathfrak{m}_O$, and $s$ sends the closed point to the image of $x$ under the first projection followed by $i_1$ followed by $bc$.
--
--   This supplies the rationality input for the crossings of the two-chart model of $X_1(Mp)$ over $A$: each point of the intersection scheme of the two components of the geometric special fibre is an $O/\mathfrak{m}_O$-valued point of $X \times_A \operatorname{Spec} O$ lying over the closed point. It is used in the construction of the oriented étale crossing chart for this model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_forall_exists_spec_hom_pullback_comp_snd_eq_and_base_closedPoint_eq_of_surjective_twoChartModel_x1_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JOnePGeom
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_JOnePOpsV2
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_WeilDatum
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_MvPolynomial_CrossingResolutionScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MvPolynomial CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SmoothProperCurve AlgebraicCurve

theorem ModularCurve.XOneP.forall_exists_spec_hom_pullback_comp_snd_eq_and_base_closedPoint_eq_of_surjective_twoChartModel_x1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] [Algebra A k]
    (C₁ C₂ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k)) (i₂ : SchemeHomOver c₂ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k))
    [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hcover : ∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hred : IsReduced (pullback i₁.1 i₂.1)) (n : ℕ) (hn : Nat.card ↥(pullback i₁.1 i₂.1) = n) (hn0 : 0 < n)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (ρO : A →+* O) (toκ : O →+* k) (htoκ : toκ.comp ρO = algebraMap A k) (hsurj : Function.Surjective toκ)
    (bc : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρO)))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom toκ)) :
    ∀ x : ↥(pullback i₁.1 i₂.1),
      ∃ s : Spec (CommRingCat.of (IsLocalRing.ResidueField O)) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρO)),
        s ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)) ∧
        s.base (IsLocalRing.closedPoint (IsLocalRing.ResidueField O)) = (pullback.fst i₁.1 i₂.1 ≫ i₁.1 ≫ bc).base x := by sorry

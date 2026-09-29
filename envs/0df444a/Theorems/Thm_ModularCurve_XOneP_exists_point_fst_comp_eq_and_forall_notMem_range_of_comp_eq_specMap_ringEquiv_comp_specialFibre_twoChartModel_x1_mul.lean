-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_point_fst_comp_eq_and_forall_notMem_range_of_comp_eq_specMap_ringEquiv_comp_specialFibre_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.exists_point_fst_comp_eq_and_forall_notMem_range_of_comp_eq_specMap_ringEquiv_comp_specialFibre_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/06feca19-e7b0-57f2-8408-e78d141b5b57
-- title:
--   Twisting a k-point of the first component off the crossings
-- statement:
--   Fix a prime $p$ and $M$ with $5 \le M$ and $p \nmid M$; let $L$ be a characteristic-zero field that is a cyclotomic extension of $\mathbb{Q}$ of order $\{p\}$, with $\zeta \in L$ a primitive $p$-th root of unity, and let $K \subseteq \mathrm{LaurentSeries}\,L$ be the intermediate field obtained by adjoining to $L$ the image under the coefficientwise map [`ModularCurve.coeffEmb`](def/ModularCurve_LaurentCoeff.html#L81) of the function field [`ModularCurve.x1FunctionField (M * p)`](def/ModularCurve_X1.html#L137) of $X_1(Mp)$ over $\mathbb{Q}$. Let $A$ be a discrete valuation domain with fraction field $L$ such that $p$ lies in the maximal ideal of $A$ and $\zeta$ is in the image of $A$, with $K$ an $A$-algebra compatibly with $A \to L \to K$, and let $j \in K$, $j \neq 0$, have image $\mathrm{coeffEmb}_L(\mathrm{jq})$ in $\mathrm{LaurentSeries}\,L$. Write $X \to \operatorname{Spec} A$ for the structure morphism [`ModularCurve.TwoChart.modelTo A K j`](def/ModularCurve_TwoChartModel.html#L252) of the two-chart model attached to these data. Let $k$ be an algebraically closed field of characteristic $p$ which is an $A$-algebra, and let $X_k := X \times_{\operatorname{Spec} A} \operatorname{Spec} k$ be the base change along $\operatorname{Spec} k \to \operatorname{Spec} A$. Let $c_1 : C_1 \to \operatorname{Spec} k$ and $c_2 : C_2 \to \operatorname{Spec} k$ be proper, smooth of relative dimension $1$ and geometrically integral, and let $i_1, i_2$ be closed immersions of $C_1$, $C_2$ into $X_k$ commuting with the structure morphisms to $\operatorname{Spec} k$, such that every point of $X_k$ lies in the image of $i_1$ or of $i_2$, the scheme-theoretic intersection $C_1 \times_{X_k} C_2$ is reduced, and its number of points is $n > 0$. The assertion is: for every ring automorphism $\sigma$ of $k$ with $\sigma \circ (A \to k) = (A \to k)$, every section $c$ of $c_1$ (a $k$-point of $C_1$) and every $y : \operatorname{Spec} k \to X_k$ that is a section of the projection to $\operatorname{Spec} k$, if $y$ followed by the projection $X_k \to X$ equals $\operatorname{Spec}(\sigma)$ followed by $c$, $i_1$ and the projection $X_k \to X$, and no point in the image of the underlying map of $c$ lies in the image of the first projection $C_1 \times_{X_k} C_2 \to C_1$, then there is a section $c'$ of $c_1$ with $c'$ followed by $i_1$ equal to $y$, with the image of the underlying map of $c'$ again disjoint from the image of $C_1 \times_{X_k} C_2 \to C_1$, and with $c'$ and $c$ sending the closed point of $\operatorname{Spec} k$ to the same point of $X$ after composing with $i_1$ and the projection $X_k \to X$.
--
--   This records that an automorphism of the base field $k$ over $A$ carries a $k$-point of the first component of the geometric special fibre of the two-chart model of $X_1(Mp)$ at $p$, lying off the crossing locus of the two components, to a $k$-point of the same component, still off the crossings and lying over the same point of the model over $A$. It is the transport step used twice in the Frobenius computations on Hecke divisors at level $Mp$, for the two-chart model and for the Igusa model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_point_fst_comp_eq_and_forall_notMem_range_of_comp_eq_specMap_ringEquiv_comp_specialFibre_twoChartModel_x1_mul.lean

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
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ModularCurve_X1HeckeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SmoothProperCurve AlgebraicCurve

theorem ModularCurve.XOneP.exists_point_fst_comp_eq_and_forall_notMem_range_of_comp_eq_specMap_ringEquiv_comp_specialFibre_twoChartModel_x1_mul
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
    (hred : IsReduced (pullback i₁.1 i₂.1)) (n : ℕ) (hn : Nat.card ↥(pullback i₁.1 i₂.1) = n) (hn0 : 0 < n) :
    ∀ (σk : k ≃+* k), (σk : k →+* k).comp (algebraMap A k) = algebraMap A k →
    ∀ (c : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁) (y : Spec (CommRingCat.of k) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)),
      y ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) = 𝟙 _ →
      y ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) =
        Spec.map (CommRingCat.ofHom (σk : k →+* k)) ≫ c.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) →
      (∀ t, c.1.base t ∉ Set.range (pullback.fst i₁.1 i₂.1).base) →
      ∃ c' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁,
        c'.1 ≫ i₁.1 = y ∧
        (∀ t, c'.1.base t ∉ Set.range (pullback.fst i₁.1 i₂.1).base) ∧
        (c'.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base (IsLocalRing.closedPoint k) =
          (c.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base (IsLocalRing.closedPoint k) := by sorry

-- Prove2me | Theorems.Thm_ModularCurve_XOneP_range_subset_smoothLocus_of_reduction_eq_of_not_mem_range_valuationSubring_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.range_subset_smoothLocus_of_reduction_eq_of_not_mem_range_valuationSubring_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/9f4316be-cbe8-522a-83c4-aeecd520fdec
-- title:
--   Pl-points reducing off the crossings lie in the smooth locus
-- statement:
--   Fix a prime $p$, an integer $M \ge 5$ with $p \nmid M$, a field $L$ of characteristic zero that is a cyclotomic extension of $\mathbb{Q}$ for $\{p\}$, and a primitive $p$-th root of unity $\zeta \in L$. Let $K$ be the intermediate field of $L \subseteq \mathrm{LaurentSeries}\,L$ obtained by adjoining to $L$ the image under the coefficientwise map [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81) of the function field [`ModularCurve.x1FunctionField (M * p)`](def/ModularCurve_X1.html#L137) $\subseteq \mathrm{LaurentSeries}\,\mathbb{Q}$. Let $A$ be a discrete valuation domain with fraction field $L$ such that $p$ lies in the maximal ideal of $A$ and $\zeta$ is in the image of $A$, with $K$ an $A$-algebra compatibly with $L$, and let $j \in K$ be a nonzero element whose image in $\mathrm{LaurentSeries}\,L$ is [`ModularCurve.coeffEmb L ModularCurve.jq`](def/ModularCurve_LaurentCoeff.html#L81). Write $X \to \operatorname{Spec} A$ for the two-chart model [`ModularCurve.TwoChart.modelTo A K j`](def/ModularCurve_TwoChartModel.html#L252), assumed proper and flat, with base change to $L$ smooth of relative dimension one. Let $k$ be an algebraically closed $A$-algebra field of characteristic $p$, and let $c_1 : C_1 \to \operatorname{Spec} k$, $c_2 : C_2 \to \operatorname{Spec} k$ be proper, geometrically integral and smooth of relative dimension one, equipped with closed immersions $i_1, i_2$ over $\operatorname{Spec} k$ into the fibre $X \times_{\operatorname{Spec} A} \operatorname{Spec} k$ whose images together cover that fibre, such that $\mathrm{pullback}\,i_1\,i_2$ is reduced with finite carrier of positive cardinality $n$. Let $U$ be an open subscheme of $X$ such that $U \hookrightarrow X \to \operatorname{Spec} A$ is smooth of relative dimension one and such that every open $W$ with this property satisfies $W \le U$. Finally let $\mathrm{Pl}$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a nonunit of $\mathrm{Pl}$, together with ring maps $\rho : A \to \mathrm{Pl}$ inducing the structure map $A \to \overline{\mathbb{Q}}$ (for a fixed compatible tower $A \subseteq L \subseteq \overline{\mathbb{Q}}$) and a surjection $\pi_k : \mathrm{Pl} \to k$ with $\pi_k \circ \rho$ the structure map $A \to k$. The conclusion: for every $\xi : \operatorname{Spec} \mathrm{Pl} \to X$ over $\operatorname{Spec}\rho$ and every $k$-point $c$ of $C_1$, if the composite of $c$ with $i_1$ followed by the projection to $X$ agrees with $\operatorname{Spec}\pi_k$ followed by $\xi$, and the image of the closed point under $c$ followed by $i_1$ does not lie in the image of $i_2$, then the set-theoretic range of $\xi$ is contained in $U$.
--
--   This is the fibrewise smoothness criterion for flat morphisms of finite presentation, applied to the two-chart model of $X_1(Mp)$ over a discrete valuation ring containing $\zeta_p$: a point with values in a valuation ring of $\overline{\mathbb{Q}}$ whose reduction lies on the component $C_1$ away from the crossings with $C_2$ factors through the maximal relatively smooth open. It is used to place such sections inside the locus where they define relative effective Cartier divisors, in the results computing the relative $\mathrm{Pic}^0$ class of reductions of points on the model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_range_subset_smoothLocus_of_reduction_eq_of_not_mem_range_valuationSubring_twoChartModel_x1_mul.lean

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

theorem ModularCurve.XOneP.range_subset_smoothLocus_of_reduction_eq_of_not_mem_range_valuationSubring_twoChartModel_x1_mul
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

    [IsProper (ModularCurve.TwoChart.modelTo A (↥K) j)]

    [Algebra A (AlgebraicClosure ℚ)] [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower A L (AlgebraicClosure ℚ)]

    [Flat (ModularCurve.TwoChart.modelTo A (↥K) j)]
    (hsmL : SmoothOfRelativeDimension 1 (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L))

    (U : (ModularCurve.TwoChartModel A (↥K) j).Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ (ModularCurve.TwoChart.modelTo A (↥K) j))]
    (hUmax : ∀ W : (ModularCurve.TwoChartModel A (↥K) j).Opens, SmoothOfRelativeDimension 1 (W.ι ≫ (ModularCurve.TwoChart.modelTo A (↥K) j)) → W ≤ U)

    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (ρ : A →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap A (AlgebraicClosure ℚ))
    (πk : ↥Pl →+* k) (hAlgk : algebraMap A k = πk.comp ρ)

    (hπk : Function.Surjective πk) :
    ∀ (ξ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (ModularCurve.TwoChart.modelTo A (↥K) j)) (c : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁),
      c.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ ξ.1 →
      (c.1 ≫ i₁.1).base (IsLocalRing.closedPoint k) ∉ Set.range i₂.1.base →
      Set.range ξ.1.base ⊆ (U : Set (ModularCurve.TwoChartModel A (↥K) j)) := by sorry

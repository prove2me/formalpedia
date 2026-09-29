-- Prove2me | Theorems.Thm_ModularCurve_XOneP_germ_mem_maximalIdeal_and_ringKrullDim_stalk_le_one_of_isGenericPoint_component_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.germ_mem_maximalIdeal_and_ringKrullDim_stalk_le_one_of_isGenericPoint_component_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/3f927b55-4217-599c-96c2-db1c6b939a83
-- title:
--   Germ of a uniformiser and stalk dimension at a component's generic point
-- statement:
--   Fix a prime $p$, an integer $M \neq 0$ with $5 \le M$ and $p \nmid M$, a characteristic-zero field $L$ that is a cyclotomic extension of $\mathbb{Q}$ of order $\{p\}$, and a primitive $p$-th root of unity $\zeta \in L$. Let $K$ be an intermediate field of $L \subseteq L((q))$ equal to [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103), i.e. the subfield generated over $L$ by the image, under the coefficientwise map [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81), of the function field `x1FunctionFieldC ℚ (M * p)` inside $\mathbb{Q}((q))$. Let $A$ be a discrete valuation ring with fraction field $L$ such that $p$ lies in the maximal ideal of $A$ and $\zeta$ is in the image of $A$, with $K$ an $A$-algebra compatibly with $A \subseteq L \subseteq K$. Let $j \in K$ be nonzero with image in $L((q))$ the coefficientwise image of the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) of the modular invariant. Let $k$ be an algebraically closed field of characteristic $p$ and an $A$-algebra. Let $c : C \to \operatorname{Spec} k$ be proper, smooth of relative dimension $1$ and geometrically integral, and let $i$ be a morphism from $C$ to the pullback of [`ModularCurve.TwoChart.modelTo A ↥K j`](def/ModularCurve_TwoChartModel.html#L252) along $\operatorname{Spec} k \to \operatorname{Spec} A$ whose composite with the second projection is $c$, with $i$ a closed immersion. The assertion: for every $\varpi \in A$ generating the maximal ideal of $A$ and every generic point $\xi$ of the whole space of $C$, writing $z$ for the image of $\xi$ under $i$ followed by the first projection to the two-chart integral model $X =$ [`AlgebraicCurve.TwoChartIntegralModel A ↥K j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) (the pushout glueing the spectra of the subalgebras `chartAlg A ↥K {j}` and `chartAlg A ↥K {j⁻¹}` of $K$), the germ at $z$ of the global section of $X$ obtained from $\varpi$ by the isomorphism $A \cong \Gamma(\operatorname{Spec} A)$ and pullback along the structure morphism [`AlgebraicCurve.TwoChartIntegralModel.toBase A ↥K j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L258) lies in the maximal ideal of the local ring $\mathcal{O}_{X,z}$, and $\dim \mathcal{O}_{X,z} \le 1$.
--
--   This records the two local properties at the image in the integral model of the generic point of a component of the geometric special fibre of the two-chart model of $X_1(Mp)$ over $A$: a uniformiser of $A$ becomes a non-unit there, and the local ring has Krull dimension at most one. It is the input to the lemmas that identify such a stalk as a discrete valuation ring of $K$ lying over $p$, and to the subsequent statements about the components of the special fibre and their sections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_germ_mem_maximalIdeal_and_ringKrullDim_stalk_le_one_of_isGenericPoint_component_twoChartModel_x1_mul.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicGeometry.SmoothProperCurve

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open scoped TensorProduct

theorem ModularCurve.XOneP.germ_mem_maximalIdeal_and_ringKrullDim_stalk_le_one_of_isGenericPoint_component_twoChartModel_x1_mul
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

    (C : Scheme.{0}) (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (i : SchemeHomOver c (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k)) [IsClosedImmersion i.1] :
    ∀ (ϖ : A), IsLocalRing.maximalIdeal A = Ideal.span {ϖ} →
    ∀ ξ : ↥C, IsGenericPoint ξ ⊤ →
      ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ ((i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base ξ) trivial).hom
          (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ))
        ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base ξ)) ∧
      ringKrullDim ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base ξ)) ≤ 1 := by sorry

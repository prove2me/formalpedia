-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_minimalPrimes_pair_mem_range_iff_le_of_fst_eq_iotaFin_specialFibre_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.exists_minimalPrimes_pair_mem_range_iff_le_of_fst_eq_iotaFin_specialFibre_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/01c97bb3-0192-5c1c-8ed9-642c99372383
-- title:
--   Two minimal primes over varpi match the two special-fibre components
-- statement:
--   Fix a prime $p$, an integer $M \neq 0$ with $5 \le M$ and $p \nmid M$, a field $L$ of characteristic zero which is a $p$-cyclotomic extension of $\mathbb{Q}$, and a primitive $p$-th root of unity $\zeta \in L$. Let $K$ be the intermediate field of $L \subseteq \operatorname{LaurentSeries} L$ obtained by adjoining to $L$ the coefficientwise image under [`ModularCurve.coeffEmb`](def/ModularCurve_LaurentCoeff.html#L81) of the function field [`ModularCurve.x1FunctionField (M * p)`](def/ModularCurve_X1.html#L137) of $X_1(Mp)$ over $\mathbb{Q}$. Let $A$ be a discrete valuation ring with fraction field $L$ such that $p$ lies in its maximal ideal and $\zeta$ is in the image of $A$, with $K$ an $A$-algebra compatibly with the tower $A \to L \to K$, and let $j \in K$ be nonzero with image in $\operatorname{LaurentSeries} L$ equal to the coefficientwise image of the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157). Let $k$ be an algebraically closed $A$-algebra field of characteristic $p$. Write $R =$ [`ModularCurve.TwoChart.chartAlgFin A K j`](def/ModularCurve_TwoChartModel.html#L135) for the $A$-subalgebra of elements of $K$ integral over $A[j]$, $X_{\mathrm{Fin}} = \operatorname{Spec} R$ with its chart morphism [`ModularCurve.TwoChart.ιFin`](def/ModularCurve_TwoChartModel.html#L231) into the two-chart model, whose structure morphism to $\operatorname{Spec} A$ is [`ModularCurve.TwoChart.modelTo`](def/ModularCurve_TwoChartModel.html#L252), glued from $\operatorname{Spec}$ of the $j$-finite and $j^{-1}$-finite chart algebras. Let $C_1, C_2$ be schemes, proper, smooth of relative dimension $1$ and geometrically integral over $\operatorname{Spec} k$, equipped with closed immersions $i_1, i_2$ into the base change of the two-chart model along $\operatorname{Spec} k \to \operatorname{Spec} A$, commuting with the morphisms to $\operatorname{Spec} k$, and assume every point of that base change (the geometric special fibre) lies in the image of $i_1$ or of $i_2$. Finally let $\varpi$ generate the maximal ideal of $A$. Then there are two distinct ideals $\mathfrak{p}_1 \neq \mathfrak{p}_2$ of $R$, each a minimal prime of $\varpi R$, which are the only minimal primes of $\varpi R$, and such that for every point $x$ of the geometric special fibre and every point $y$ of $X_{\mathrm{Fin}}$ whose chart image agrees with the image of $x$ under the first projection, one has $x \in \operatorname{range} i_a$ if and only if $\mathfrak{p}_a \subseteq \mathfrak{p}_y$, for $a = 1, 2$.
--
--   This is the dictionary, for the two-chart integral model of $X_1(Mp)$ over a discrete valuation ring with residue characteristic $p$, between the two irreducible components of the geometric special fibre and the two minimal primes over a uniformiser in the $j$-finite chart ring; classically the mod-$p$ fibre of $X_1(Mp)$ consists of two copies of $X_1(M)$. It is used in the subsequent analysis of the components via Hecke degeneracy maps and of the behaviour at points lying on a prescribed minimal prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_minimalPrimes_pair_mem_range_iff_le_of_fst_eq_iotaFin_specialFibre_twoChartModel_x1_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X1HeckeOperator
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicGeometry.SmoothProperCurve

theorem ModularCurve.XOneP.exists_minimalPrimes_pair_mem_range_iff_le_of_fst_eq_iotaFin_specialFibre_twoChartModel_x1_mul
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
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ}) :
    ∃ (𝔭₁ 𝔭₂ : Ideal ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)),
      𝔭₁ ∈ (Ideal.span {algebraMap A ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ϖ}).minimalPrimes ∧
      𝔭₂ ∈ (Ideal.span {algebraMap A ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ϖ}).minimalPrimes ∧
      𝔭₁ ≠ 𝔭₂ ∧
      (∀ 𝔭 ∈ (Ideal.span {algebraMap A ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ϖ}).minimalPrimes, 𝔭 = 𝔭₁ ∨ 𝔭 = 𝔭₂) ∧
      ∀ (x : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k))) (y : ↥(ModularCurve.TwoChart.XFin A (↥K) j)),
        (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base x = (ModularCurve.TwoChart.ιFin A (↥K) j).base y →
          (x ∈ Set.range i₁.1.base ↔ 𝔭₁ ≤ y.asIdeal) ∧
          (x ∈ Set.range i₂.1.base ↔ 𝔭₂ ≤ y.asIdeal) := by sorry

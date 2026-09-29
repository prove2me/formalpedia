-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_mem_minimalPrimes_iotaFin_eq_and_eq_of_isDomain_tensorProduct_quotient_specialFibre_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.exists_mem_minimalPrimes_iotaFin_eq_and_eq_of_isDomain_tensorProduct_quotient_specialFibre_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/12210c1d-8cbc-51ab-8f28-68103c87f227
-- title:
--   Components of the geometric special fibre over chart primes
-- statement:
--   Fix a prime $p$ and a natural number $M$ with $5 \le M$ and $p \nmid M$, a field $L$ of characteristic zero that is a $\{p\}$-cyclotomic extension of $\mathbb{Q}$, and a primitive $p$-th root of unity $\zeta \in L$. Let $K$ be an intermediate field of $L \subseteq L((q))$, assumed equal to $L$-adjoined to the coefficientwise image in $L((q))$ of the $q$-expansion function field of $X_1(Mp)$ over $\mathbb{Q}$. Let $A$ be a discrete valuation domain with fraction field $L$, with $p$ in its maximal ideal, with $\zeta$ in the image of $A$, and with an $A$-algebra structure on $K$ compatible with $A \to L \to K$; let $\varpi$ generate the maximal ideal of $A$, and let $k$ be an algebraically closed $A$-algebra field with $\varpi \mapsto 0$. Let $j \in K$, nonzero, have image in $L((q))$ the coefficientwise image of the $q$-expansion $jq$. Write $R =$ `chartAlgFin` $A$ $K$ $j$, the subalgebra of elements of $K$ integral over $A[j]$, $X_{\mathrm{fin}} = \operatorname{Spec} R$ with its morphism `ιFin` into the two-chart pushout model, and form the pullback of the model's structure morphism to $\operatorname{Spec} A$ along $\operatorname{Spec} k \to \operatorname{Spec} A$. Two assertions are made. First, every irreducible component $Z$ of this pullback admits a point $y \in X_{\mathrm{fin}}$ whose prime ideal is a minimal prime over $\varpi R$ and with `ιFin` of $y$ equal to the image of the generic point of $Z$ under the first projection. Second, if $y \in X_{\mathrm{fin}}$ has prime ideal a minimal prime over $\varpi R$ and $k \otimes_A (R/y)$ is a domain, then any two irreducible components whose generic points both project to `ιFin` of $y$ coincide.
--
--   This locates the irreducible components of the geometric special fibre of the two-chart integral model of $X_1(Mp)$ over the minimal primes of the $j$-finite chart ring above the uniformiser, the centres of the chart's discrete valuations, and shows that a component is unique over such a prime whose residue ring stays a domain after base change to $k$. It is used in the subsequent analysis of that special fibre, in particular in the statements about branch ideals in the stalks and about uniqueness of the component over a given chart prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_mem_minimalPrimes_iotaFin_eq_and_eq_of_isDomain_tensorProduct_quotient_specialFibre_twoChartModel_x1_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve
open scoped TensorProduct

theorem ModularCurve.XOneP.exists_mem_minimalPrimes_iotaFin_eq_and_eq_of_isDomain_tensorProduct_quotient_specialFibre_twoChartModel_x1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (k : Type) [Field k] [IsAlgClosed k] [Algebra A k] (hϖk : algebraMap A k ϖ = 0) :

    (∀ (Z : Set ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)))
        (hZ : Z ∈ irreducibleComponents ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k))),
        ∃ y : ↥(ModularCurve.TwoChart.XFin A (↥K) j),
          y.asIdeal ∈ (Ideal.span {algebraMap A ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ϖ}).minimalPrimes ∧
          (ModularCurve.TwoChart.ιFin A (↥K) j).base y =
            (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base hZ.1.genericPoint) ∧

    (∀ (y : ↥(ModularCurve.TwoChart.XFin A (↥K) j)),
        y.asIdeal ∈ (Ideal.span {algebraMap A ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ϖ}).minimalPrimes →
        IsDomain (k ⊗[A] (↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ⧸ y.asIdeal)) →
        ∀ (Z₁ Z₂ : Set ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)))
          (hZ₁ : Z₁ ∈ irreducibleComponents ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)))
          (hZ₂ : Z₂ ∈ irreducibleComponents ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k))),
          (ModularCurve.TwoChart.ιFin A (↥K) j).base y =
              (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base hZ₁.1.genericPoint →
          (ModularCurve.TwoChart.ιFin A (↥K) j).base y =
              (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base hZ₂.1.genericPoint →
          Z₁ = Z₂) := by sorry

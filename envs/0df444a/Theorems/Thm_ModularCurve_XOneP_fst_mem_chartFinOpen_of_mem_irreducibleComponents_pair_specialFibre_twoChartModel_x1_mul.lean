-- Prove2me | Theorems.Thm_ModularCurve_XOneP_fst_mem_chartFinOpen_of_mem_irreducibleComponents_pair_specialFibre_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.fst_mem_chartFinOpen_of_mem_irreducibleComponents_pair_specialFibre_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/a6209bf6-eddf-5dac-b5b7-86073aa38ec7
-- title:
--   Crossings in a geometric fibre lie in the j-finite chart
-- statement:
--   Let $p$ be a prime, $M$ a nonzero natural number with $5 \le M$ and $p \nmid M$, and let $L$ be a field of characteristic zero that is a cyclotomic extension of $\mathbb{Q}$ of type $\{p\}$, with $\zeta \in L$ a primitive $p$-th root of unity. Let $K$ be an intermediate field of $L((q)) =$ `LaurentSeries L` over $L$, assumed equal to [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103), i.e. the subfield generated over $L$ by the image, under the coefficientwise map [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81) induced by $\mathbb{Q} \to L$, of the $q$-expansion function field of $X_1(Mp)$ over $\mathbb{Q}$. Let $A$ be a discrete valuation domain with fraction field $L$ such that $p$ lies in the maximal ideal of $A$ and $\zeta$ is in the image of $A \to L$, with an $A$-algebra structure on $K$ compatible with $A \to L \to K$. Let $j \in K$ be nonzero with image in $L((q))$ equal to [`ModularCurve.coeffEmb L ModularCurve.jq`](def/ModularCurve_LaurentCoeff.html#L81), the $q$-expansion $q^{-1}\cdot j_{\mathrm{num}}$ of the modular invariant. Let $k$ be an algebraically closed field which is an $A$-algebra, and form the base change $P$ of the structure morphism [`ModularCurve.TwoChart.modelTo A K j`](def/ModularCurve_TwoChartModel.html#L252) of the two-chart model (the pushout of `fFin` and `fInf`) along $\operatorname{Spec} k \to \operatorname{Spec} A$. Then for every point $x$ of $P$ lying on two distinct irreducible components $Z_1 \ne Z_2$ of $P$, the image of $x$ under the first projection $P \to$ `TwoChartModel A K j` lies in the open set [`ModularCurve.TwoChart.chartFinOpen A K j`](def/ModularCurve_TwoChartModel.html#L280), the range of the chart immersion `ιFin`, i.e. the $j$-finite chart.
--
--   This is the statement that the crossing points of a geometric fibre of the two-chart integral model of $X_1(Mp)$ over $A$ occur only in the $j$-finite chart: the fibre is regular along the cuspidal locus $j = \infty$, whereas a point lying on two distinct irreducible components has a non-regular local ring. It is used in the analysis of the special fibre at $p$ of $X_1(Mp)$, in particular by the statements locating crossing points in the intersection of the two chart ranges and comparing stalks at crossings with Gauss valuation rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_fst_mem_chartFinOpen_of_mem_irreducibleComponents_pair_specialFibre_twoChartModel_x1_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve

theorem ModularCurve.XOneP.fst_mem_chartFinOpen_of_mem_irreducibleComponents_pair_specialFibre_twoChartModel_x1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (k : Type) [Field k] [IsAlgClosed k] [Algebra A k]
    (x : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)))
    (Z₁ Z₂ : Set ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)))
    (hZ₁ : Z₁ ∈ irreducibleComponents ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k))) (hZ₂ : Z₂ ∈ irreducibleComponents ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)))
    (hne : Z₁ ≠ Z₂) (hx₁ : x ∈ Z₁) (hx₂ : x ∈ Z₂) :
    (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base x ∈ ModularCurve.TwoChart.chartFinOpen A (↥K) j := by sorry

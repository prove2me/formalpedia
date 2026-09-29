-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_modularUnit_mem_chartAlgFin_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.exists_modularUnit_mem_chartAlgFin_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/9f37585a-87c7-5adf-9548-4af6d232d3d3
-- title:
--   Modular units Δ(q)/Δ(qᵖ) in the finite-j chart of X₁(Mp)
-- statement:
--   Let $p$ be a prime and $M$ a nonzero natural number with $5 \le M$ and $p \nmid M$. Let $L$ be a field of characteristic zero that is a cyclotomic extension of $\mathbb{Q}$ for the set $\{p\}$, and let $\zeta \in L$ be a primitive $p$-th root of unity. Let $K$ be an intermediate field of $L((q))$ over $L$ which equals [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103), i.e. the subfield of $L((q))$ generated over $L$ by the image, under the coefficientwise map [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81) induced by $\mathbb{Q} \to L$, of the $q$-expansion function field [`ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 (M * p))`](def/ModularCurve_X1.html#L101) attached to $\Gamma_1(Mp)$. Let $A$ be a discrete valuation ring which is a domain with fraction field $L$, such that $p$ lies in the maximal ideal of $A$ and $\zeta$ is in the image of $A$, with an $A$-algebra structure on $K$ compatible with that on $L$. Let $j \in K$ be nonzero with image in $L((q))$ equal to the coefficientwise image of [`ModularCurve.jq`](def/ModularCurve_X0.html#L157), the Laurent series $q^{-1}$ times the rational power series [`ModularCurve.jNumQ`](def/ModularCurve_X0.html#L149). Then there exist $u, u'$ in [`ModularCurve.TwoChart.chartAlgFin A K j`](def/ModularCurve_TwoChartModel.html#L135), the subalgebra of elements of $K$ integral over $A[j]$, whose images in $L((q))$ are respectively the coefficientwise image of [`ModularCurve.modularUnitSeries p`](def/ModularCurve_ModularUnit.html#L127) $= \Delta(q)/\Delta(q^p)$ (the product of [`ModularCurve.deltaSeries`](def/ModularCurve_ModularUnit.html#L107) with the inverse of its substitution $q \mapsto q^p$) and $p^{12}$ times the inverse of that image, and which satisfy $u u' = p^{12}$ in that subalgebra.
--
--   The statement provides the modular unit $\Delta(\tau)/\Delta(p\tau)$ on $X_0(p)$, pulled back to $X_1(Mp)$, together with its companion $p^{12}\Delta(p\tau)/\Delta(\tau)$, as a pair of elements of the finite-$j$ chart ring of the two-chart model of $X_1(Mp)$ over $A$ whose product is $p^{12}$. It supplies the input for the Deligne–Rapoport style level-polynomial and finite étale quotient constructions on this model, being cited by [`ModularCurve.XOneP.exists_finite_etale_quotient_span_aeval_chartAlgFin_twoChartModel_x1_mul`](thm.html#ModularCurve.XOneP.exists_finite_etale_quotient_span_aeval_chartAlgFin_twoChartModel_x1_mul) and [`ModularCurve.XOneP.exists_oneSidedPool_smoothLocus_twoChartModel_x1_mul`](thm.html#ModularCurve.XOneP.exists_oneSidedPool_smoothLocus_twoChartModel_x1_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_modularUnit_mem_chartAlgFin_twoChartModel_x1_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_ModularUnit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial

theorem ModularCurve.XOneP.exists_modularUnit_mem_chartAlgFin_twoChartModel_x1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)] :
    ∃ u u' : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j),
      ((u : ↥K) : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.modularUnitSeries p) ∧
      ((u' : ↥K) : LaurentSeries L) = (p : LaurentSeries L) ^ 12 * (ModularCurve.coeffEmb L (ModularCurve.modularUnitSeries p))⁻¹ ∧
      u * u' = (p : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) ^ 12 := by sorry

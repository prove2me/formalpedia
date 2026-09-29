-- Prove2me | Theorems.Thm_ModularCurve_mem_chartAlgFin_and_forall_mem_chartAlgInf_exists_mul_mem_of_coe_eq_coeffEmb_jq_qExpand
-- name    : ModularCurve.mem_chartAlgFin_and_forall_mem_chartAlgInf_exists_mul_mem_of_coe_eq_coeffEmb_jq_qExpand
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/4691e322-6366-5a01-85e6-9ad86b9b86d2
-- title:
--   Mutual integrality of j(q) and j(qᵖ) on two-chart models
-- statement:
--   Let $p$ be a prime, let $L$ be a field of characteristic zero, let $K$ be an intermediate field of the Laurent series field $L((q))$ over $L$, and let $A$ be a commutative domain equipped with an $L$-algebra structure making $L$ the fraction field of $A$, together with a compatible $A$-algebra structure on $K$ (an `IsScalarTower A L ↥K`). Let $j \in K$ be nonzero whose image in $L((q))$ is [`ModularCurve.coeffEmb L ModularCurve.jq`](def/ModularCurve_LaurentCoeff.html#L81), the coefficientwise image along $\mathbb{Q} \to L$ of the Laurent series $q^{-1}\cdot(\text{power series } j_{\mathrm{Num}})$, and let $j' \in K$ be nonzero whose image is the coefficientwise image of [`ModularCurve.qExpand ℚ p ModularCurve.jq`](def/ModularCurve_X0.html#L25), i.e. of the same series with its exponents multiplied by $p$ (substitution $q \mapsto q^p$). For $x \in K^\times$ write $\mathcal{O}_{\mathrm{fin}}(x)$ and $\mathcal{O}_\infty(x)$ for the subalgebras `chartAlgFin` and `chartAlgInf` of $K$, namely the elements of $K$ integral over $A[x]$, respectively over $A[x^{-1}]$. The conclusion is the conjunction of four assertions: $j' \in \mathcal{O}_{\mathrm{fin}}(j)$; $j \in \mathcal{O}_{\mathrm{fin}}(j')$; every $y \in \mathcal{O}_\infty(j')$ admits $s \in \mathcal{O}_\infty(j)$ of the form $s = 1 + j^{-1}a$ with $a \in \mathcal{O}_\infty(j)$ and $sy \in \mathcal{O}_\infty(j)$; and the same statement with the roles of $j$ and $j'$ interchanged.
--
--   The content is the level-$p$ modular equation relating $j(q)$ and $j(q^p)$, which is monic of degree $\psi(p) = p+1$ in each variable and symmetric in the two variables, expressed as integrality of each of $j, j'$ over the finite chart algebra of the other together with a mutual comparability condition at the cusp charts. These four assertions are exactly the hypotheses of the comparison result identifying the two-chart integral models of $K$ over $A$ built from $j$ and from $j(q^p)$, and they are used in the full-level analysis of maximal ideals of the finite chart algebra and of supersingular points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_mem_chartAlgFin_and_forall_mem_chartAlgInf_exists_mul_mem_of_coe_eq_coeffEmb_jq_qExpand.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem ModularCurve.mem_chartAlgFin_and_forall_mem_chartAlgInf_exists_mul_mem_of_coe_eq_coeffEmb_jq_qExpand
    (p : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (j' : ↥K) (hj' : ((j' : LaurentSeries L)) = ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ p ModularCurve.jq)) [Fact (j' ≠ 0)] :
    j' ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j ∧
    j ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j' ∧
    (∀ y ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j', ∃ s ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j,
      (∃ a ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j, s = 1 + j⁻¹ * a) ∧ s * y ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j) ∧
    (∀ y ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j, ∃ s ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j',
      (∃ a ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j', s = 1 + j'⁻¹ * a) ∧ s * y ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j') := by sorry

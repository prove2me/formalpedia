-- Prove2me | Theorems.Thm_ModularCurve_mem_maximalIdeal_apply_of_coe_mem_nonunits_gauss_of_mem_chartAlgInf_laurentBaseChange
-- name    : ModularCurve.mem_maximalIdeal_apply_of_coe_mem_nonunits_gauss_of_mem_chartAlgInf_laurentBaseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/3ee1d740-712d-5856-ba4c-9cca1fa739b6
-- title:
--   q-expansion principle at ∞: Gauss non-units have constant term in mathfrak m_A
-- statement:
--   Let $\Gamma$ be a subgroup of $\mathrm{SL}_2(\mathbb Z)$, let $L$ be a field of characteristic zero, and let $K$ be an intermediate field of $L \subseteq L((q))$ equal to [`ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ)`](def/ModularCurve_LaurentCoeff.html#L103), that is, the subfield of $L((q))$ generated over $L$ by the coefficientwise images under $\mathbb Q \to L$ of the subfield of $\mathbb Q((q))$ generated over $\mathbb Q$ by the quotients `intSeriesC ℚ pf / intSeriesC ℚ pg` attached to pairs of modular forms $f,g$ of a common weight $k$ for $\Gamma$ (viewed in $\mathrm{GL}_2(\mathbb R)$) with integral $q$-expansions $pf, pg \in \mathbb Z[[q]]$, the denominator series being non-zero. Let $A$ be a discrete valuation ring which is an $A$-subalgebra of $L$ with $L$ its fraction field, together with a compatible $A$-algebra structure on $K$. Let $j \in K$ be non-zero with Laurent expansion the coefficientwise image of $q^{-1}\,j_{\mathrm{num}}(q)$, the $q$-expansion of the modular invariant. Let $W_0$ be a valuation subring of $K$ whose members are exactly the $f$ admitting a presentation $f \cdot \hat y = \hat x$ in $L((q))$ with $x,y \in A[[q]]$, $\hat{\;}$ denoting the image of a power series over $A$ in $L((q))$, and $y$ having non-zero reduction modulo the maximal ideal of $A$. Write $A_\infty$ for [`ModularCurve.TwoChart.chartAlgInf A K j`](def/ModularCurve_TwoChartModel.html#L137), the $A$-subalgebra of elements of $K$ integral over $A[j^{-1}]$. Let $\psi \colon A_\infty \to A$ be a ring homomorphism such that $\psi(f)$, mapped into $L$, is the $q^0$-coefficient of the Laurent expansion of $f$, and assume every $f \in A_\infty$ has vanishing coefficients in all negative degrees. Then $A_\infty \subseteq W_0$, and every $b \in A_\infty$ lying in the set of non-units of $W_0$ satisfies $\psi(b) \in \mathfrak m_A$.
--
--   This is the $q$-expansion principle at the cusp $\infty$ in the form needed to see that the cusp specialises into the Gauss component: the centre of the Gauss valuation ring on the pole chart of the two-chart integral model is contained in the prime cut out by the constant-term map. It rests on the integrality statement [`ModularCurve.exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartModel_laurentBaseChange`](thm.html#ModularCurve.exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartModel_laurentBaseChange), and it feeds the constant-term results for the two-chart integral model at full level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_mem_maximalIdeal_apply_of_coe_mem_nonunits_gauss_of_mem_chartAlgInf_laurentBaseChange.lean

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.mem_maximalIdeal_apply_of_coe_mem_nonunits_gauss_of_mem_chartAlgInf_laurentBaseChange
    (Γ : Subgroup SL(2, ℤ))
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))

    (ψ : ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j) →+* A)
    (hψ0 : ∀ f : ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j),
      algebraMap A L (ψ f) = (((f : ↥K) : LaurentSeries L)).coeff 0)
    (hord : ∀ f : ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j), ∀ k : ℤ, k < 0 →
      (((f : ↥K) : LaurentSeries L)).coeff k = 0) :
    (∀ b : ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j), ((b : ↥K)) ∈ W₀) ∧
    (∀ b : ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j), ((b : ↥K)) ∈ W₀.nonunits →
      ψ b ∈ IsLocalRing.maximalIdeal A) := by sorry

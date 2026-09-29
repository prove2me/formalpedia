-- Prove2me | Theorems.Thm_ModularCurve_isMaximal_of_jInvChartInf_mem_of_forall_mem_nonunits_gauss_chartAlgInf
-- name    : ModularCurve.isMaximal_of_jInvChartInf_mem_of_forall_mem_nonunits_gauss_chartAlgInf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/9e448018-9c04-5c3f-b8fd-71992a3ea5c2
-- title:
--   Maximality at the cusp of the j⁻¹-chart
-- statement:
--   Let $\Gamma$ be a subgroup of $\mathrm{SL}_2(\mathbb{Z})$, let $L$ be a field of characteristic zero, and let $K$ be an intermediate field of $L \subseteq L((q))$ assumed equal to the subfield of $L((q))$ generated over $L$ by the coefficientwise image under $\mathbb{Q} \to L$ of the $q$-expansion function field of level $\Gamma$, namely the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the quotients of integral $q$-expansion series attached to pairs of modular forms of equal weight on $\Gamma$ admitting integral $q$-expansions (denominator series nonzero). Let $A$ be a discrete valuation domain with an $L$-algebra structure making $L$ its fraction field, together with a $K$-algebra structure compatible with $L \subseteq K$, and let $\varpi \in A$ generate the maximal ideal. Let $j \in K$ be nonzero with image in $L((q))$ the coefficientwise image of $q^{-1}$ times the power series $j$-numerator over $\mathbb{Q}$. Let $W_0$ be a valuation subring of $K$ consisting exactly of those $f$ for which there exist $x,y \in A[[q]]$ with $y$ nonzero modulo the maximal ideal of $A$ and $f \cdot \hat y = \hat x$ in $L((q))$, where $\hat{\,\cdot\,}$ denotes the image of a power series over $A$ in $L((q))$. Let $B \subseteq K$ be the subalgebra of elements integral over $A[j^{-1}]$, and let $\mathfrak y \subseteq B$ be a prime ideal containing the image of $\varpi$, containing $j^{-1}$, and containing every element of $B$ whose image in $K$ is a nonunit of $W_0$. Then $\mathfrak y$ is a maximal ideal of $B$.
--
--   This identifies the prime $(\varpi, j^{-1})$-type points of the $j^{-1}$-chart of the two-chart integral model of the modular curve — the points lying over the cusp in the special fibre, dominated by the Gauss valuation — as closed points. It is used in the verification that the local rings of the integral model at such points are regular, in the full-level analysis of the fibres of the chart algebra.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isMaximal_of_jInvChartInf_mem_of_forall_mem_nonunits_gauss_chartAlgInf.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem ModularCurve.isMaximal_of_jInvChartInf_mem_of_forall_mem_nonunits_gauss_chartAlgInf
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (y : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j)) [y.IsPrime]
    (hϖy : algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j) ϖ ∈ y)
    (hcusp : AlgebraicCurve.TwoChartIntegralModel.jInvChartInf A (↥K) j ∈ y)
    (hz₀ : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j), (b : ↥K) ∈ W₀.nonunits → b ∈ y) :
    y.IsMaximal := by sorry

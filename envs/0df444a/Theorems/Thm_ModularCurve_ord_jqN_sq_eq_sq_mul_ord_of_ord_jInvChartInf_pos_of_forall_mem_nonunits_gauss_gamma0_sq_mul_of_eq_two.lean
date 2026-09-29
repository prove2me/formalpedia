-- Prove2me | Theorems.Thm_ModularCurve_ord_jqN_sq_eq_sq_mul_ord_of_ord_jInvChartInf_pos_of_forall_mem_nonunits_gauss_gamma0_sq_mul_of_eq_two
-- name    : ModularCurve.ord_jqN_sq_eq_sq_mul_ord_of_ord_jInvChartInf_pos_of_forall_mem_nonunits_gauss_gamma0_sq_mul_of_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/cbb7a4d8-7fa8-5908-bdff-c16ce9d9c838
-- title:
--   Gauss-branch cusp: ord_w J₂ = q²ord_w j for q=2
-- statement:
--   Let $q$ be a prime with $q = 2$, let $M'$ be a nonzero natural number not divisible by $q$, and let $L$ be a field of characteristic zero that is algebraic over $\mathbb{Q}$. Let $K$ be an intermediate field of $L \subseteq \mathrm{LaurentSeries}\,L$ equal to [`ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (q ^ 2 * M')))`](def/ModularCurve_LaurentCoeff.html#L103), that is, the subfield of $L((\mathsf{q}))$ generated over $L$ by the coefficientwise image under [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81) of the subfield of $\mathbb{Q}((\mathsf{q}))$ generated over $\mathbb{Q}$ by the ratios of integral forms `intFormRatiosC` for $\Gamma_0(q^2M')$. Let $A$ be a discrete valuation ring which is a domain with fraction field $L$, with $q$ lying in its maximal ideal and $\varpi$ a generator of that maximal ideal, and let $K$ be an $A$-algebra compatibly with $A \to L \to K$. Let $j \in K$ be the element whose Laurent expansion is [`ModularCurve.coeffEmb L ModularCurve.jq`](def/ModularCurve_LaurentCoeff.html#L81), the expansion $\mathsf{q}^{-1}$ times the power series `jNumQ`, and assume $j \neq 0$; let $J_2 \in K$ have Laurent expansion [`ModularCurve.coeffEmb L (ModularCurve.jqN (q ^ 2))`](def/ModularCurve_LaurentCoeff.html#L81), the image of `jq` under substitution $\mathsf{q} \mapsto \mathsf{q}^{q^2}$. Let $W_0$ be a valuation subring of $K$ consisting exactly of those $f$ for which there are power series $x, y$ over $A$ with $y$ having nonzero reduction modulo the maximal ideal of $A$ and $f \cdot y = x$ after mapping coefficients into $L$. Let $w$ be a place of $K$ over $L$ (a proper valuation subring containing the image of $L$ and whose ideals are principal), with associated order function $\operatorname{ord}_w = -\log$ of its adic valuation, and assume $\operatorname{ord}_w(j^{-1}) > 0$, where $j^{-1}$ is taken as the element `jInvChartInf` of the chart algebra $A_\infty =$ `chartAlgInf A K j`, the $A$-subalgebra of elements of $K$ integral over $A[j^{-1}]$. Finally let $y$ be a maximal ideal of $A_\infty$ containing the image of $\varpi$, containing every element of $A_\infty$ whose image in $K$ is a non-unit of $W_0$, and containing every element $b$ of $A_\infty$ with $\operatorname{ord}_w(b) > 0$. Then $\operatorname{ord}_w(J_2) = q^2 \cdot \operatorname{ord}_w(j)$ in $\mathbb{Z}$.
--
--   This is the criterion identifying, for a cusp place $w$ of the base-changed function field of $X_0(q^2M')$ which specialises into the Gauss branch of the pole chart, the order of vanishing of $j(q^2\tau)$ as $q^2$ times that of $j$; it is the case $q = 2$ of the statement, matching the case of larger primes. It feeds the computation that the ramification index along the inclusion of the $\Gamma_0$-level field equals one at such places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ord_jqN_sq_eq_sq_mul_ord_of_ord_jInvChartInf_pos_of_forall_mem_nonunits_gauss_gamma0_sq_mul_of_eq_two.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_SupersingularModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open scoped MatrixGroups

theorem ModularCurve.ord_jqN_sq_eq_sq_mul_ord_of_ord_jInvChartInf_pos_of_forall_mem_nonunits_gauss_gamma0_sq_mul_of_eq_two
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L] [Algebra.IsAlgebraic ℚ L]

    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (q ^ 2 * M'))))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))

    (J₂ : ↥K) (hJ₂ : ((J₂ : LaurentSeries L)) = ModularCurve.coeffEmb L (ModularCurve.jqN (q ^ 2)))
    (w : AlgebraicCurve.Place L ↥K)
    (hw : 0 < w.ord ((AlgebraicCurve.TwoChartIntegralModel.jInvChartInf A (↥K) j :
      ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j)) : ↥K))
    (y : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j)) [y.IsMaximal]
    (hyϖ : algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j) ϖ ∈ y)
    (hz₀ : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j), (b : ↥K) ∈ W₀.nonunits → b ∈ y)
    (hwy : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j), 0 < w.ord (b : ↥K) → b ∈ y) :
    w.ord J₂ = (q : ℤ) ^ 2 * w.ord (j : ↥K) := by sorry

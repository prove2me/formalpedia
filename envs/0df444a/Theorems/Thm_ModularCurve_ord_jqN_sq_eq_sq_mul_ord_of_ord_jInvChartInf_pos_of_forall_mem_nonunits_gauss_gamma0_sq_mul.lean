-- Prove2me | Theorems.Thm_ModularCurve_ord_jqN_sq_eq_sq_mul_ord_of_ord_jInvChartInf_pos_of_forall_mem_nonunits_gauss_gamma0_sq_mul
-- name    : ModularCurve.ord_jqN_sq_eq_sq_mul_ord_of_ord_jInvChartInf_pos_of_forall_mem_nonunits_gauss_gamma0_sq_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/96487143-42ec-5b28-b750-cb15b504990e
-- title:
--   Cusps on the Gauss branch: ord_w j(q²τ)=q² ord_w j
-- statement:
--   Let $q$ be a prime with $q\ge 5$, let $M'$ be a nonzero natural number with $q\nmid M'$, and let $L$ be a field of characteristic zero that is algebraic over $\mathbb Q$. Let $K\subseteq L((\mathsf q))$ be the intermediate field obtained from [`ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (q ^ 2 * M'))`](def/ModularCurve_X1.html#L101) — the subfield of $\mathbb Q((\mathsf q))$ generated over $\mathbb Q$ by `intFormRatiosC` for $\Gamma_0(q^2M')$ — by applying the coefficientwise map [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81) induced by $\mathbb Q\to L$ and adjoining the image to $L$. Let $A$ be a discrete valuation domain with fraction field $L$, compatibly acting on $K$, with $q$ in the maximal ideal of $A$ and $\varpi$ a generator of that maximal ideal. Let $j\in K$ be nonzero with $\mathsf q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157), and $J_2\in K$ with $\mathsf q$-expansion [`ModularCurve.jqN (q ^ 2)`](def/ModularCurve_X0.html#L194), i.e. `jq` with exponents multiplied by $q^2$. Let $W_0$ be a valuation subring of $K$ consisting exactly of those $f$ for which $f\cdot y=x$ in $L((\mathsf q))$ for some power series $x,y$ over $A$ with $y$ having nonzero reduction modulo the maximal ideal. Let $w$ be a place of $K$ over $L$ (a valuation subring of $K$ containing $L$, not all of $K$, and a principal ideal ring), with $\mathrm{ord}_w(j^{-1})>0$, where $j^{-1}$ is viewed in the chart algebra of elements of $K$ integral over $A[j^{-1}]$. Let $y$ be a maximal ideal of that chart algebra containing $\varpi$, containing every element whose image in $K$ is a non-unit of $W_0$, and containing every element of positive $w$-order. Then $\mathrm{ord}_w J_2=q^2\,\mathrm{ord}_w j$.
--
--   This is the $\infty$-type (Gauss branch) incidence criterion for cusps: a place of the function field of $X_0(q^2M')$ at which $j$ has a pole and which specialises into a closed point of the Gauss component of the pole chart satisfies $\mathrm{ord}_w j(q^2\tau)=q^2\,\mathrm{ord}_w j(\tau)$. It is used by [`ModularCurve.ramificationIndexAlong_inclusion_gamma0_eq_one_of_ord_jInvChartInf_pos_of_forall_mem_nonunits_gauss_gamma0_sq_mul`](thm.html#ModularCurve.ramificationIndexAlong_inclusion_gamma0_eq_one_of_ord_jInvChartInf_pos_of_forall_mem_nonunits_gauss_gamma0_sq_mul) to show that the ramification index along the corresponding inclusion of modular function fields equals one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ord_jqN_sq_eq_sq_mul_ord_of_ord_jInvChartInf_pos_of_forall_mem_nonunits_gauss_gamma0_sq_mul.lean

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

theorem ModularCurve.ord_jqN_sq_eq_sq_mul_ord_of_ord_jInvChartInf_pos_of_forall_mem_nonunits_gauss_gamma0_sq_mul
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
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

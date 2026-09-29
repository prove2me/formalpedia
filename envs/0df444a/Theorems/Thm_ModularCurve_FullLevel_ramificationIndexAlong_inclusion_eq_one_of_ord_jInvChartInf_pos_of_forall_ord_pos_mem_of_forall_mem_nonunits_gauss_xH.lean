-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_ramificationIndexAlong_inclusion_eq_one_of_ord_jInvChartInf_pos_of_forall_ord_pos_mem_of_forall_mem_nonunits_gauss_xH
-- name    : ModularCurve.FullLevel.ramificationIndexAlong_inclusion_eq_one_of_ord_jInvChartInf_pos_of_forall_ord_pos_mem_of_forall_mem_nonunits_gauss_xH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/6905121f-7764-5730-9906-8f7657a5492e
-- title:
--   Cusps on the Gauss branch are unramified over X₀(M')
-- statement:
--   Let $q\ge 5$ be a prime, let $M'$ be a nonzero natural number not divisible by $q$, and let $L$ be a field of characteristic zero algebraic over $\mathbb{Q}$. Let $K$ be an intermediate field of $L \subseteq \operatorname{LaurentSeries} L$ equal to [`ModularCurve.laurentBaseChange L`](def/ModularCurve_LaurentCoeff.html#L103) applied to [`ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')`](def/ModularCurve_XH.html#L79), i.e. the subfield of $L((\mathsf q))$ generated over $L$ by the coefficientwise images of the $\mathbb{Q}$-rational $q$-expansion function field of $X_H(q^2M')$ for $H$ the kernel of the reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$. Let $A$ be a discrete valuation domain with $L$ as fraction field, with $q$ in its maximal ideal, acting on $K$ compatibly with $L$, and let $\varpi$ generate the maximal ideal of $A$. Let $j \in K$, nonzero, have image in $L((\mathsf q))$ the coefficientwise image of [`ModularCurve.jq`](def/ModularCurve_X0.html#L157). Let $W_0$ be a valuation subring of $K$ consisting exactly of those $f$ for which there are power series $x,y$ over $A$ with $y$ not reducing to $0$ modulo the maximal ideal and $f \cdot y_L = x_L$ in $L((\mathsf q))$ (the Gauss valuation ring). Let $K_0$ be the $L$-base change of [`ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')`](def/ModularCurve_X1.html#L101), with $K_0 \le K$. Let $w$ be a place of $K$ over $L$ (a proper valuation subring containing $L$ whose ideals are principal) with $\operatorname{ord}_w(j^{-1}) > 0$, where $j^{-1}$ is taken in the subalgebra [`AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A K j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L144) of elements of $K$ integral over $A[j^{-1}]$. Let $y$ be a maximal ideal of that subalgebra which contains $\varpi$, contains every element whose image in $K$ is a nonunit of $W_0$, and contains every element $b$ with $\operatorname{ord}_w(b) > 0$. Then the ramification index of $w$ along the inclusion $K_0 \hookrightarrow K$ equals $1$; that is, the least $n > 0$ for which some nonzero $f \in K_0$ has $\operatorname{ord}_w(f) = n$ is $1$.
--
--   This is the cuspidal case of the horizontal-ramification analysis for $X_H(q^2M')$ over the $X_0(M')$-floor: a place of $K$ at which $1/j$ has positive order and whose specialisation lies on the closed point $y$ of the Gauss (infinity-Igusa) branch contributes no width, so the cusp is unramified over $K_0$. It feeds the unramifiedness statement [`ModularCurve.FullLevel.isUnramifiedAt_of_height_one_of_algebraMap_not_mem_chartAlgInf_of_jInvChartInf_mem_xH`](thm.html#ModularCurve.FullLevel.isUnramifiedAt_of_height_one_of_algebraMap_not_mem_chartAlgInf_of_jInvChartInf_mem_xH).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_ramificationIndexAlong_inclusion_eq_one_of_ord_jInvChartInf_pos_of_forall_ord_pos_mem_of_forall_mem_nonunits_gauss_xH.lean

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

theorem ModularCurve.FullLevel.ramificationIndexAlong_inclusion_eq_one_of_ord_jInvChartInf_pos_of_forall_ord_pos_mem_of_forall_mem_nonunits_gauss_xH
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L] [Algebra.IsAlgebraic ℚ L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (K₀ : IntermediateField L (LaurentSeries L))
    (hK₀ : K₀ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')))
    (hle₀ : K₀ ≤ K)
    (w : AlgebraicCurve.Place L ↥K)
    (hw : 0 < w.ord ((AlgebraicCurve.TwoChartIntegralModel.jInvChartInf A (↥K) j :
      ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j)) : ↥K))
    (y : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j)) [y.IsMaximal]
    (hyϖ : algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j) ϖ ∈ y)
    (hz₀ : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j), (b : ↥K) ∈ W₀.nonunits → b ∈ y)
    (hwy : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j), 0 < w.ord (b : ↥K) → b ∈ y) :
    AlgebraicCurve.Place.ramificationIndexAlong (IntermediateField.inclusion hle₀) w = 1 := by sorry

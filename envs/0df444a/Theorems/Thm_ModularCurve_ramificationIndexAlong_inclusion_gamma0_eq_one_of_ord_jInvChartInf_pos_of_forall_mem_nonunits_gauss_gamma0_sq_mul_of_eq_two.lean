-- Prove2me | Theorems.Thm_ModularCurve_ramificationIndexAlong_inclusion_gamma0_eq_one_of_ord_jInvChartInf_pos_of_forall_mem_nonunits_gauss_gamma0_sq_mul_of_eq_two
-- name    : ModularCurve.ramificationIndexAlong_inclusion_gamma0_eq_one_of_ord_jInvChartInf_pos_of_forall_mem_nonunits_gauss_gamma0_sq_mul_of_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/f7f04979-fdf7-54c6-bb64-275bc2909511
-- title:
--   Unramifiedness over X₀(M') at an ∞-type cusp place, q=2
-- statement:
--   Let $q$ be a prime with $q=2$, let $M'$ be a nonzero natural number not divisible by $q$, and let $L$ be a field of characteristic zero that is algebraic over $\mathbb{Q}$. Let $K$ be the intermediate field of $\mathrm{LaurentSeries}\,L$ over $L$ equal to [`ModularCurve.laurentBaseChange`](def/ModularCurve_LaurentCoeff.html#L103) of the $q$-expansion function field `qExpFunctionFieldC ℚ (Gamma0 (q ^ 2 * M'))`, i.e. the field generated over $L$ by the coefficientwise images of that rational function field, and let $K_0$ be the corresponding field for $\Gamma_0(M')$, with $K_0 \le K$. Let $A$ be a discrete valuation domain with fraction field $L$, with $q$ in its maximal ideal, $\varpi$ a generator of that maximal ideal, and with an $A$-algebra structure on $K$ compatible with $L$. Let $j \in K$ be nonzero with Laurent series the coefficient image of `jq` $= T^{-1}\cdot jNumQ$, and let $W_0$ be a valuation subring of $K$ whose members are exactly those $f$ for which there are power series $x,y$ over $A$ with $y$ having nonzero reduction modulo the maximal ideal and $f \cdot y = x$ in $\mathrm{LaurentSeries}\,L$. Let $w$ be a place of $K$ over $L$ (a proper valuation subring containing $L$, with principal ideals) such that $\mathrm{ord}_w(j^{-1}) > 0$, where $j^{-1}$ is taken in the subalgebra `chartAlgInf A K j` of elements of $K$ integral over $A[j^{-1}]$. Let $y$ be a maximal ideal of that subalgebra containing the image of $\varpi$, containing every element whose image in $K$ is a nonunit of $W_0$, and containing every element of strictly positive $w$-order. Then the ramification index of $w$ along the inclusion $K_0 \hookrightarrow K$ — the least $n>0$ of the form $\mathrm{ord}_w(f)$ for a nonzero $f \in K_0$ — equals $1$.
--
--   The assertion is that a cusp place of $X_0(q^2M')$ lying on the $\infty$-type component of the reduction, cut out by the Gauss valuation ring $W_0$ of $A$-integral $\mathsf{q}$-expansions and specialising into the closed point $y$ of the pole chart, is unramified over $X_0(M')$; this is the $q=2$ case. It feeds the corresponding statement at full level $X_H$, used in the analysis of semistable coverings of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ramificationIndexAlong_inclusion_gamma0_eq_one_of_ord_jInvChartInf_pos_of_forall_mem_nonunits_gauss_gamma0_sq_mul_of_eq_two.lean

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

theorem ModularCurve.ramificationIndexAlong_inclusion_gamma0_eq_one_of_ord_jInvChartInf_pos_of_forall_mem_nonunits_gauss_gamma0_sq_mul_of_eq_two
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

-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_ramificationIndexAlong_inclusion_gamma0_sq_mul_eq_one_of_ord_jInvChartInf_pos_of_forall_mem_nonunits_gauss_xH_of_eq_two
-- name    : ModularCurve.FullLevel.ramificationIndexAlong_inclusion_gamma0_sq_mul_eq_one_of_ord_jInvChartInf_pos_of_forall_mem_nonunits_gauss_xH_of_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/1447f7e0-be74-5a89-b6d2-f8e2bc97123c
-- title:
--   Unramifiedness over X₀(q²M') at an ∞-Igusa cusp place, q=2
-- statement:
--   Let $q$ be a prime with $q = 2$, let $M'$ be a nonzero natural number not divisible by $q$, and let $L$ be a field of characteristic zero that is algebraic over $\mathbb Q$. Let $K$ be the intermediate field of $L \subseteq \mathrm{LaurentSeries}\,L$ obtained as [`ModularCurve.laurentBaseChange`](def/ModularCurve_LaurentCoeff.html#L103) of the function field [`ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')`](def/ModularCurve_XH.html#L79), that is, the field generated over $L$ by the coefficientwise images of the $q$-expansions of the $X_H$-level-$(q^2M')$ field for $H =$ the kernel of the unit-reduction map `ZMod.unitsMap` attached to the divisibility `dvd_sq_mul q M'`. Let $A$ be a discrete valuation domain with fraction field $L$, with $q$ in its maximal ideal, with uniformiser $\varpi$, and with an $A$-algebra structure on $K$ compatible with $L$. Let $j \in K$ be a nonzero element whose Laurent expansion is the image of [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) under [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81). Let $W_0$ be a valuation subring of $K$ consisting exactly of those $f$ for which there are power series $x, y$ over $A$ with $y$ having nonzero reduction modulo the maximal ideal of $A$ and $f \cdot y = x$ as Laurent series over $L$. Let $K_2$ be the base change to $L$ of the $q$-expansion field of $\Gamma_0(q^2M')$, assumed contained in $K$. Let $w$ be a place of $K$ over $L$ (a proper valuation subring containing $L$ whose ideals are principal) with $w.\mathrm{ord}(j^{-1}) > 0$, where $j^{-1}$ is taken in the subalgebra `chartAlgInf` of elements of $K$ integral over $A[j^{-1}]$. Let $y$ be a maximal ideal of that subalgebra which contains $\varpi$, contains every element whose image in $K$ is a nonunit of $W_0$, and contains every element of positive $w$-order. Then the ramification index along the inclusion $K_2 \hookrightarrow K$ at $w$ — the least $n > 0$ of the form $w.\mathrm{ord}(f)$ for some nonzero $f \in K_2$ — equals $1$.
--
--   This is the statement that a cusp place of $X_H(q^2M')$ lying on the $\infty$-branch of the Igusa tower (the branch cut out by the valuation subring $W_0$ of ratios of integral power series with unit denominator) is unramified over the intermediate floor $X_0(q^2M')$, in the case $q = 2$. It is the $q = 2$ case feeding the combined statement [`ModularCurve.FullLevel.ramificationIndexAlong_inclusion_eq_one_of_ord_jInvChartInf_pos_of_forall_ord_pos_mem_of_forall_mem_nonunits_gauss_xH_of_eq_two`](thm.html#ModularCurve.FullLevel.ramificationIndexAlong_inclusion_eq_one_of_ord_jInvChartInf_pos_of_forall_ord_pos_mem_of_forall_mem_nonunits_gauss_xH_of_eq_two), used in the analysis of the semistable covering $X_H(q^2M') \to X_0(q^2M')$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_ramificationIndexAlong_inclusion_gamma0_sq_mul_eq_one_of_ord_jInvChartInf_pos_of_forall_mem_nonunits_gauss_xH_of_eq_two.lean

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

theorem ModularCurve.FullLevel.ramificationIndexAlong_inclusion_gamma0_sq_mul_eq_one_of_ord_jInvChartInf_pos_of_forall_mem_nonunits_gauss_xH_of_eq_two
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
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

    (K₂ : IntermediateField L (LaurentSeries L))
    (hK₂ : K₂ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (q ^ 2 * M'))))
    (hle₂ : K₂ ≤ K)
    (w : AlgebraicCurve.Place L ↥K)
    (hw : 0 < w.ord ((AlgebraicCurve.TwoChartIntegralModel.jInvChartInf A (↥K) j :
      ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j)) : ↥K))
    (y : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j)) [y.IsMaximal]
    (hyϖ : algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j) ϖ ∈ y)
    (hz₀ : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j), (b : ↥K) ∈ W₀.nonunits → b ∈ y)
    (hwy : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j), 0 < w.ord (b : ↥K) → b ∈ y) :
    AlgebraicCurve.Place.ramificationIndexAlong (IntermediateField.inclusion hle₂) w = 1 := by sorry

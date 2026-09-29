-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_ramificationIndexAlong_inclusion_eq_one_of_ord_jInvChartInf_pos_of_forall_ord_pos_mem_of_forall_mem_nonunits_gauss_xH_of_eq_three
-- name    : ModularCurve.FullLevel.ramificationIndexAlong_inclusion_eq_one_of_ord_jInvChartInf_pos_of_forall_ord_pos_mem_of_forall_mem_nonunits_gauss_xH_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/673a33ea-93f4-5879-9e42-030ec22004d9
-- title:
--   Unramifiedness over the X₀(M') floor at ∞-branch cusps, q=3
-- statement:
--   Fix a prime $q$ with $q = 3$ and a nonzero natural number $M'$ with $q \nmid M'$; let $L$ be a field of characteristic zero algebraic over $\mathbb{Q}$. Let $K$ be an intermediate field of $L \subseteq L((\mathsf q))$ equal to [`ModularCurve.laurentBaseChange L`](def/ModularCurve_LaurentCoeff.html#L103) of [`ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')`](def/ModularCurve_XH.html#L79), that is, the subfield of $L((\mathsf q))$ generated over $L$ by the coefficientwise image of the function field attached to the level $q^2M'$ and the subgroup `levelH q M'`, the kernel of the map of unit groups `ZMod.unitsMap` associated with the divisibility `dvd_sq_mul q M'`. Let $A$ be a discrete valuation ring, a domain with $L$ as fraction field, with $q$ in its maximal ideal, $\varpi$ a generator of that maximal ideal, and with an $A$-algebra structure on $K$ compatible with $L$. Let $j \in K$ be nonzero with image in $L((\mathsf q))$ the coefficientwise image of [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) $= \mathsf q^{-1}\cdot(\text{power series } jNumQ)$. Let $W_0$ be the valuation subring of $K$ consisting of those $f$ for which there are power series $x, y$ over $A$ with $y$ having nonzero reduction modulo the maximal ideal and $f \cdot y = x$ in $L((\mathsf q))$ (the Gauss valuation ring). Let $K_0 =$ `laurentBaseChange L` of `qExpFunctionFieldC ℚ (Gamma0 M')` and assume $K_0 \le K$. Let $w$ be a place of $K$ over $L$ (a valuation subring containing $L$, proper, with principal ideals) with $\operatorname{ord}_w(j^{-1}) > 0$, where $j^{-1}$ is taken in `chartAlgInf A K j`, the ring of elements of $K$ integral over $A[j^{-1}]$. Let $y$ be a maximal ideal of that ring containing $\varpi$, containing every element whose image in $K$ is a nonunit of $W_0$, and containing every element $b$ with $\operatorname{ord}_w(b) > 0$. Then the ramification index along the inclusion $K_0 \hookrightarrow K$ at $w$, namely the least positive $n$ of the form $\operatorname{ord}_w(f)$ for some nonzero $f \in K_0$, equals $1$.
--
--   This is the statement that a cusp of $X_H(q^2M')$ whose specialisation lies on the $\infty$-branch (the Gauss, or Igusa, branch) is unramified over the $X_0(M')$ floor, in the case $q = 3$, where the Igusa covering of that branch is trivial. It feeds the unramifiedness statement [`ModularCurve.FullLevel.isUnramifiedAt_of_height_one_of_algebraMap_not_mem_chartAlgInf_of_jInvChartInf_mem_xH_of_eq_three`](thm.html#ModularCurve.FullLevel.isUnramifiedAt_of_height_one_of_algebraMap_not_mem_chartAlgInf_of_jInvChartInf_mem_xH_of_eq_three) in the analysis of the integral model of the modular curve at $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_ramificationIndexAlong_inclusion_eq_one_of_ord_jInvChartInf_pos_of_forall_ord_pos_mem_of_forall_mem_nonunits_gauss_xH_of_eq_three.lean

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

theorem ModularCurve.FullLevel.ramificationIndexAlong_inclusion_eq_one_of_ord_jInvChartInf_pos_of_forall_ord_pos_mem_of_forall_mem_nonunits_gauss_xH_of_eq_three
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
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

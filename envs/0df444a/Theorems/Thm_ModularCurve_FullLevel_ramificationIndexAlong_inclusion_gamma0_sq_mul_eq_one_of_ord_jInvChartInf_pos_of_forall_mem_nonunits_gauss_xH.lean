-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_ramificationIndexAlong_inclusion_gamma0_sq_mul_eq_one_of_ord_jInvChartInf_pos_of_forall_mem_nonunits_gauss_xH
-- name    : ModularCurve.FullLevel.ramificationIndexAlong_inclusion_gamma0_sq_mul_eq_one_of_ord_jInvChartInf_pos_of_forall_mem_nonunits_gauss_xH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/8aed3712-b6ce-552a-a75c-b506db13410f
-- title:
--   Igusa-branch cusps are unramified over the Γ₀(q²M') floor
-- statement:
--   Let $q\ge 5$ be a prime, let $M'$ be a nonzero natural number not divisible by $q$, and let $L$ be a field of characteristic zero algebraic over $\mathbb Q$. Let $K$ be the intermediate field of $L\subseteq L((X))$ obtained by adjoining to $L$ the coefficientwise image of the function field [`ModularCurve.xHFunctionField (q ^ 2 * M')`](def/ModularCurve_XH.html#L79) at the subgroup $H$ of $(\mathbb Z/q^2M')^\times$ given by the kernel of reduction to $(\mathbb Z/q)^\times$. Let $A$ be a discrete valuation ring with fraction field $L$, with $q$ in its maximal ideal, with $\varpi$ generating that ideal, and with $K$ an $A$-algebra compatibly with $A\to L\to K$. Let $j\in K$, $j\neq 0$, have image in $L((X))$ the coefficientwise image of the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) of the modular invariant. Let $W_0$ be a valuation subring of $K$ consisting exactly of the elements $f$ for which there are power series $x,y$ over $A$ with $y$ having nonzero reduction modulo the maximal ideal and $f\cdot y = x$ in $L((X))$ after mapping coefficients to $L$. Let $K_2\le K$ be the intermediate field obtained by adjoining to $L$ the coefficientwise image of [`ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (q ^ 2 * M'))`](def/ModularCurve_X1.html#L101). Let $w$ be a place of $K$ over $L$ (a proper valuation subring containing $L$ whose ideals are principal) with $w.\mathrm{ord}(j^{-1})>0$, where $j^{-1}$ is taken in the subalgebra $B$ of elements of $K$ integral over $A[j^{-1}]$. Let $y$ be a maximal ideal of $B$ containing the image of $\varpi$, containing every $b\in B$ whose image in $K$ is a nonunit of $W_0$, and containing every $b\in B$ with $w.\mathrm{ord}(b)>0$. Then the ramification index of $w$ along the inclusion $K_2\hookrightarrow K$ — the least positive integer of the form $w.\mathrm{ord}(f)$ for nonzero $f\in K_2$ — equals $1$.
--
--   This is the statement that a cusp of $X_H(q^2M')$ lying on the Igusa branch at $\infty$ in characteristic $q$ is unramified over the intermediate floor $X_0(q^2M')$, the corresponding widths agreeing because the stabiliser in $\Gamma_0(q^2M')$ of such a cusp already lies in $\Gamma_H(q^2M')\cdot\{\pm 1\}$. It is the $\Gamma_0(q^2M')$ variant of the analogous statement over the $\Gamma_0(M')$ floor, and feeds the computation of ramification indices at cusps used in the study of the integral model of $X_H(q^2M')$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_ramificationIndexAlong_inclusion_gamma0_sq_mul_eq_one_of_ord_jInvChartInf_pos_of_forall_mem_nonunits_gauss_xH.lean

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

theorem ModularCurve.FullLevel.ramificationIndexAlong_inclusion_gamma0_sq_mul_eq_one_of_ord_jInvChartInf_pos_of_forall_mem_nonunits_gauss_xH
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

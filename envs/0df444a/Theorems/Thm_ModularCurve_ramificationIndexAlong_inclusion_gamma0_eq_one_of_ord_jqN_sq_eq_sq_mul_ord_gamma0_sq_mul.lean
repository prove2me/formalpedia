-- Prove2me | Theorems.Thm_ModularCurve_ramificationIndexAlong_inclusion_gamma0_eq_one_of_ord_jqN_sq_eq_sq_mul_ord_gamma0_sq_mul
-- name    : ModularCurve.ramificationIndexAlong_inclusion_gamma0_eq_one_of_ord_jqN_sq_eq_sq_mul_ord_gamma0_sq_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/865d56d5-9a68-586c-a847-41ed04e95044
-- title:
--   Cusps of ∞-type on X₀(q²M') are unramified over X₀(M')
-- statement:
--   Fix a prime $q$ with $q \ge 5$ and a nonzero natural number $M'$ with $q \nmid M'$, and let $L$ be a field of characteristic zero that is algebraic over $\mathbb{Q}$. Let $K$ be an intermediate field of $L \subseteq L((\mathsf q))$ assumed equal to [`ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (q ^ 2 * M')))`](def/ModularCurve_LaurentCoeff.html#L103), i.e. the subfield of $L((\mathsf q))$ generated over $L$ by the coefficientwise images under $\mathbb{Q} \to L$ of the field generated over $\mathbb{Q}$ inside $\mathbb{Q}((\mathsf q))$ by the quotients of integral $q$-expansions of pairs of modular forms of equal weight for $\Gamma_0(q^2M')$; let $K_0 \le K$ be the corresponding field for level $M'$. Let $j, J_2 \in K$ be the elements whose Laurent series are the coefficientwise images of [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) (that is, $\mathsf q^{-1}$ times the integral $j$-numerator power series) and of [`ModularCurve.jqN (q ^ 2)`](def/ModularCurve_X0.html#L194), the substitution $\mathsf q \mapsto \mathsf q^{q^2}$ applied to it. Let $w$ be a place of $K$ over $L$, meaning a valuation subring of $K$ containing $L$, proper and a principal ideal ring, with $\operatorname{ord}_w j < 0$ and $\operatorname{ord}_w J_2 = q^2 \operatorname{ord}_w j$. Then the ramification index of $w$ along the inclusion $K_0 \hookrightarrow K$, the least $n > 0$ of the form $\operatorname{ord}_w f$ for a nonzero $f \in K_0$, equals $1$.
--
--   This is the statement that the cusps of $X_0(q^2M')$ of "$\infty$-type", characterised valuation-theoretically by $\operatorname{ord}_w j(q^2\tau) = q^2 \operatorname{ord}_w j(\tau)$, are unramified in the covering $X_0(q^2M') \to X_0(M')$. It feeds the analysis of the local behaviour of the covering at cusps used in the study of the modular curves attached to level $q^2M'$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ramificationIndexAlong_inclusion_gamma0_eq_one_of_ord_jqN_sq_eq_sq_mul_ord_gamma0_sq_mul.lean

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

theorem ModularCurve.ramificationIndexAlong_inclusion_gamma0_eq_one_of_ord_jqN_sq_eq_sq_mul_ord_gamma0_sq_mul
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L] [Algebra.IsAlgebraic ℚ L]

    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (q ^ 2 * M'))))
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq)

    (J₂ : ↥K) (hJ₂ : ((J₂ : LaurentSeries L)) = ModularCurve.coeffEmb L (ModularCurve.jqN (q ^ 2)))

    (K₀ : IntermediateField L (LaurentSeries L))
    (hK₀ : K₀ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')))
    (hle₀ : K₀ ≤ K)

    (w : AlgebraicCurve.Place L ↥K) (hw : w.ord j < 0)
    (hP : w.ord J₂ = (q : ℤ) ^ 2 * w.ord j) :
    AlgebraicCurve.Place.ramificationIndexAlong (IntermediateField.inclusion hle₀) w = 1 := by sorry

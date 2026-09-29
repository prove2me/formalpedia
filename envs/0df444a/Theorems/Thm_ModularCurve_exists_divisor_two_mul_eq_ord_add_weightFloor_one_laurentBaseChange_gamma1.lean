-- Prove2me | Theorems.Thm_ModularCurve_exists_divisor_two_mul_eq_ord_add_weightFloor_one_laurentBaseChange_gamma1
-- name    : ModularCurve.exists_divisor_two_mul_eq_ord_add_weightFloor_one_laurentBaseChange_gamma1
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/999eb0f0-c36f-54fe-9d6f-784051a0f2d8
-- title:
--   Divisor of a weight-one form on X₁(M), M≥ 5
-- statement:
--   Let $M$ be a natural number with $5 \le M$, and let $F$ denote the intermediate field [`ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))`](def/ModularCurve_LaurentCoeff.html#L103) of $\mathbb{C}((q))$: that is, the subfield generated over $\mathbb{C}$ by the coefficientwise images under $\mathbb{Q} \to \mathbb{C}$ of the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the ratios $p_f/p_g$ of integral $q$-expansions of modular forms $f, g$ of a common weight for $\Gamma_1(M)$ (with $p_g \neq 0$ in the Laurent series field). Assume given: an element $y \in F$ whose underlying Laurent series is [`ModularCurve.jqModC ℂ`](def/ModularCurve_JqCoeff.html#L15), namely $q^{-1}$ times the power series $E_4^3 \cdot \eta^{-24}$ over $\mathbb{C}$, so the $q$-expansion of $j$; a nonzero modular form $w$ of weight $1$ for $\Gamma_1(M)$; and an element $v \in F$ such that, in $\mathbb{C}((q))$, the product of $v$ with $\vartheta(j(q)) = q\,\frac{d}{dq} j(q)$ equals the square of the $q$-expansion of $w$. The conclusion asserts the existence of a divisor $D$ — a finitely supported $\mathbb{Z}$-valued function on the places of $F/\mathbb{C}$ — such that for every place $P$, with $\operatorname{ord}_P$ the normalised valuation attached to $P$, $$2\,D(P) = \operatorname{ord}_P(v) + \Big(\big[\tfrac{2\operatorname{ord}_P(y)}{3}\big] \text{ if } \operatorname{ord}_P(y) > 0\Big) + \Big(\big[\tfrac{\operatorname{ord}_P(y - 1728)}{2}\big] \text{ if } \operatorname{ord}_P(y-1728) > 0\Big) + \Big(\operatorname{ord}_P(y) \text{ if } \operatorname{ord}_P(y) < 0\Big),$$ the integer divisions being rounded towards $-\infty$ as in `Int` division, and each bracketed term being $0$ when its condition fails.
--
--   This is the statement that the divisor of a nonzero weight-one form on $X_1(M)$ for $M \ge 5$ is integral: the right-hand side, which is $\operatorname{div}(v) + \operatorname{div}(\vartheta j)$ written through the weight-floor recipe at $m = 1$, is divisible by $2$ at every place, reflecting the absence of elliptic points for $M \ge 4$ and the regularity of all cusps for $M \ge 5$. It feeds the dimension estimate for spaces of weight-one forms on $\Gamma_1(M)$ used in [`ModularForm.exists_linearIndependent_gamma1_dimFormula_le_card_of_odd`](thm.html#ModularForm.exists_linearIndependent_gamma1_dimFormula_le_card_of_odd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_divisor_two_mul_eq_ord_add_weightFloor_one_laurentBaseChange_gamma1.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup ModularCurve
open scoped MatrixGroups ModularForm

theorem ModularCurve.exists_divisor_two_mul_eq_ord_add_weightFloor_one_laurentBaseChange_gamma1
    (M : ℕ) [NeZero M] (hM : 5 ≤ M)
    (y : ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))))
    (hy : (y : LaurentSeries ℂ) = ModularCurve.jqModC ℂ)
    (w : ModularForm (Gamma1 M) 1) (hw : w ≠ 0)
    (v : ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))))
    (hv : (v : LaurentSeries ℂ) * ModularCurve.thetaL ℂ (ModularCurve.jqModC ℂ) =
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 w) ^ 2) :
    ∃ D : AlgebraicCurve.Divisor ℂ
        ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))),
      ∀ P : AlgebraicCurve.Place ℂ
        ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))),
        2 * D P = P.ord v +
          ((if 0 < P.ord y then (2 * P.ord y) / 3 else 0)
            + (if 0 < P.ord (y - 1728) then (P.ord (y - 1728)) / 2 else 0)
            + (if P.ord y < 0 then P.ord y else 0)) := by sorry

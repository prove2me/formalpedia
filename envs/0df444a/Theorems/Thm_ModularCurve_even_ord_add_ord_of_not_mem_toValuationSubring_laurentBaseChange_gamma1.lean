-- Prove2me | Theorems.Thm_ModularCurve_even_ord_add_ord_of_not_mem_toValuationSubring_laurentBaseChange_gamma1
-- name    : ModularCurve.even_ord_add_ord_of_not_mem_toValuationSubring_laurentBaseChange_gamma1
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/46da1d66-da83-5463-9f0e-23c8a08ce13e
-- title:
--   Even parity of ord_P v+ord_P y at cusp places
-- statement:
--   Fix a natural number $M$ with $M \neq 0$ and $5 \le M$, and let $F$ denote the intermediate field of $\mathbb{C}((q))$ over $\mathbb{C}$ obtained as [`ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))`](def/ModularCurve_LaurentCoeff.html#L103), i.e. the field generated over $\mathbb{C}$ by the coefficientwise images under $\mathbb{Q} \to \mathbb{C}$ of the elements of the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the quotients $\mathrm{intSeriesC}\,p_f/\mathrm{intSeriesC}\,p_g$ of integral $q$-expansions of two modular forms of the same weight on $\Gamma_1(M)$ (with the denominator nonzero). Let $y \in F$ have underlying Laurent series [`ModularCurve.jqModC ℂ`](def/ModularCurve_JqCoeff.html#L15), namely $q^{-1}$ times the power series $E_4^3 \cdot \eta^{-\text{unit}}$ (the series `jNum`) with coefficients pushed to $\mathbb{C}$. Let $w$ be a nonzero modular form of weight $1$ on $\Gamma_1(M)$, and let $v \in F$ satisfy, as an identity of Laurent series over $\mathbb{C}$, $v \cdot \vartheta(j) = (\text{$q$-expansion of $w$})^2$, where $\vartheta$ is the operator [`ModularCurve.thetaL`](def/ModularCurve_QExpansionDiff.html#L16) sending $f$ to $q \cdot f'$. Let $P$ be a place of $F$ over $\mathbb{C}$ in the sense of [`AlgebraicCurve.Place`](def/AlgebraicCurve_DivisorClassGroup.html#L22): a valuation subring of $F$ containing $\mathbb{C}$, not equal to all of $F$, and a principal ideal ring. Assume $y$ does not lie in that valuation subring. Then $\operatorname{ord}_P v + \operatorname{ord}_P y$ is even, where $\operatorname{ord}_P$ is minus the logarithm of the associated height-one-spectrum valuation.
--
--   The condition $y \notin \mathcal{O}_P$ singles out the cusp places of the function field of $X_1(M)$, where $j$ has a pole; the assertion is the parity statement reflecting that for $M \ge 5$ all cusps of $\Gamma_1(M)$ are regular, so that a weight-one form has integral order at each cusp. It is the cusp half of the parity input to [`ModularCurve.exists_divisor_two_mul_eq_ord_add_weightFloor_one_laurentBaseChange_gamma1`](thm.html#ModularCurve.exists_divisor_two_mul_eq_ord_add_weightFloor_one_laurentBaseChange_gamma1), which expresses the relevant divisor as twice a divisor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_even_ord_add_ord_of_not_mem_toValuationSubring_laurentBaseChange_gamma1.lean

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

theorem ModularCurve.even_ord_add_ord_of_not_mem_toValuationSubring_laurentBaseChange_gamma1
    (M : ℕ) [NeZero M] (hM : 5 ≤ M)
    (y : ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))))
    (hy : (y : LaurentSeries ℂ) = ModularCurve.jqModC ℂ)
    (w : ModularForm (Gamma1 M) 1) (hw : w ≠ 0)
    (v : ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))))
    (hv : (v : LaurentSeries ℂ) * ModularCurve.thetaL ℂ (ModularCurve.jqModC ℂ) =
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 w) ^ 2)
    (P : AlgebraicCurve.Place ℂ
        ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))))
    (hP : y ∉ P.toValuationSubring) :
    Even (P.ord v + P.ord y) := by sorry

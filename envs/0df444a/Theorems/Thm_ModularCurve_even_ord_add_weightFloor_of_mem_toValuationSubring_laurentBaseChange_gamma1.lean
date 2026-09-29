-- Prove2me | Theorems.Thm_ModularCurve_even_ord_add_weightFloor_of_mem_toValuationSubring_laurentBaseChange_gamma1
-- name    : ModularCurve.even_ord_add_weightFloor_of_mem_toValuationSubring_laurentBaseChange_gamma1
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/44bd2a0d-9100-5e11-8546-1f6573c5bdd2
-- title:
--   Interior parity of ord_P(v) plus the weight-floor term
-- statement:
--   Fix $M \ge 4$ and let $F$ be the subfield of $\mathbb{C}((q))$ obtained by adjoining to $\mathbb{C}$ the coefficientwise images under $\mathbb{Q} \to \mathbb{C}$ of the $q$-expansion function field of $\Gamma_1(M)$ over $\mathbb{Q}$, the latter being generated over $\mathbb{Q}$ by the quotients of integral $q$-expansions of two modular forms of a common weight on $\Gamma_1(M)$. Let $y \in F$ have underlying Laurent series $q^{-1}$ times the power series $E_4^3 \cdot \eta^{-24}$ with coefficients pushed to $\mathbb{C}$, i.e. the $q$-expansion of $j$. Let $w$ be a nonzero modular form of weight $1$ on $\Gamma_1(M)$, and let $v \in F$ satisfy $v \cdot \vartheta(j) = (\text{$q$-expansion of } w)^2$ in $\mathbb{C}((q))$, where $\vartheta(f) = q \, df/dq$. Let $P$ be a place of $F$ over $\mathbb{C}$ — a proper valuation subring of $F$ containing $\mathbb{C}$ and a principal ideal ring — with associated order function $\operatorname{ord}_P$, and assume $y$ lies in that valuation subring. Then the integer $$\operatorname{ord}_P(v) + \big[\operatorname{ord}_P(y)>0\big]\,\tfrac{2\operatorname{ord}_P(y)}{3} + \big[\operatorname{ord}_P(y-1728)>0\big]\,\tfrac{\operatorname{ord}_P(y-1728)}{2} + \big[\operatorname{ord}_P(y)<0\big]\,\operatorname{ord}_P(y)$$ is even, the two quotients being integer division of positive dividends.
--
--   This is the interior (non-cuspidal) half of the parity statement underlying the identification of a weight-one form on $\Gamma_1(M)$, $M \ge 4$, with a square root of $v \cdot \vartheta(j)$: at a place lying over a point of the upper half-plane, where $\Gamma_1(M)$ has no elliptic fixed points and the complex place dictionary is unramified, the order of $v$ corrected by the weight-floor term has the parity of twice the order of vanishing of $w$. It feeds the construction of a divisor $D$ with $2D = \operatorname{div}(v) + \operatorname{div}(\vartheta j)$ on $X_1(M)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_even_ord_add_weightFloor_of_mem_toValuationSubring_laurentBaseChange_gamma1.lean

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

theorem ModularCurve.even_ord_add_weightFloor_of_mem_toValuationSubring_laurentBaseChange_gamma1
    (M : ℕ) [NeZero M] (hM : 4 ≤ M)
    (y : ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))))
    (hy : (y : LaurentSeries ℂ) = ModularCurve.jqModC ℂ)
    (w : ModularForm (Gamma1 M) 1) (hw : w ≠ 0)
    (v : ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))))
    (hv : (v : LaurentSeries ℂ) * ModularCurve.thetaL ℂ (ModularCurve.jqModC ℂ) =
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 w) ^ 2)
    (P : AlgebraicCurve.Place ℂ
        ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))))
    (hP : y ∈ P.toValuationSubring) :
    Even (P.ord v +
          ((if 0 < P.ord y then (2 * P.ord y) / 3 else 0)
            + (if 0 < P.ord (y - 1728) then (P.ord (y - 1728)) / 2 else 0)
            + (if P.ord y < 0 then P.ord y else 0))) := by sorry

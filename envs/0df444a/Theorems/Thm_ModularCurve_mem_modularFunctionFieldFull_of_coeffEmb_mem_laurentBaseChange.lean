-- Prove2me | Theorems.Thm_ModularCurve_mem_modularFunctionFieldFull_of_coeffEmb_mem_laurentBaseChange
-- name    : ModularCurve.mem_modularFunctionFieldFull_of_coeffEmb_mem_laurentBaseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/c619b95a-ee1f-5348-9341-b46d0f4e96c7
-- title:
--   Descent of ℂ-compositum: rational members lie in F_N
-- statement:
--   Let $N$ be a nonzero natural number and let $x$ be a Laurent series with rational coefficients. Write $F_N :=$ [`ModularCurve.modularFunctionFieldFull N`](def/ModularCurve_X0.html#L305) for the intermediate field of $\mathbb{Q} \subseteq \mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the set `divisorExpansions N`, that is by the series `qExpand ℚ d jq` as $d$ runs over the nonzero divisors of $N$. Write `coeffEmb ℂ` for the ring homomorphism $\mathbb{Q}((q)) \to \mathbb{C}((q))$ obtained by applying the structure map $\mathbb{Q} \to \mathbb{C}$ to each coefficient, and `laurentBaseChange ℂ F_N` for the intermediate field of $\mathbb{C} \subseteq \mathbb{C}((q))$ generated over $\mathbb{C}$ by the image of $F_N$ under `coeffEmb ℂ`. The hypothesis is that the coefficientwise image of $x$ in $\mathbb{C}((q))$ lies in this compositum $\mathbb{C} \cdot F_N$. The conclusion is that $x$ itself lies in $F_N$. Thus the intersection of $\mathbb{C}\cdot F_N$ with the series having rational coefficients is no larger than $F_N$; series in $\mathbb{C}\cdot F_N$ with irrational coefficients are simply not in the scope of the assertion.
--
--   This is the descent statement $\mathbb{C}\cdot F_N \cap \mathbb{Q}((q)) = F_N$ for the formal $q$-expansion presentation of the function field of $X_0(N)$, specialised to the coefficient field $\mathbb{C}$ and to the level-$N$ field. It is used in the bounded-denominators argument, where a ratio of modular forms with rational $q$-expansion is first located in the compositum $\mathbb{C}\cdot F_N$ and must then be recognised as an element of $F_N$; it feeds [`ModularCurve.ofPowerSeries_mul_thetaL_jq_zpow_neg_mem_modularFunctionField`](thm.html#ModularCurve.ofPowerSeries_mul_thetaL_jq_zpow_neg_mem_modularFunctionField).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_mem_modularFunctionFieldFull_of_coeffEmb_mem_laurentBaseChange.lean

import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Data.Complex.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.mem_modularFunctionFieldFull_of_coeffEmb_mem_laurentBaseChange (N : ℕ) [NeZero N]
    (x : LaurentSeries ℚ)
    (hx : ModularCurve.coeffEmb ℂ x ∈
      ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)) :
    x ∈ ModularCurve.modularFunctionFieldFull N := by sorry

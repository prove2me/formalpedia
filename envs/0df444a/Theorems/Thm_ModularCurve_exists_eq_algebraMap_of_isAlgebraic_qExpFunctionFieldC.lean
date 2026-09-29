-- Prove2me | Theorems.Thm_ModularCurve_exists_eq_algebraMap_of_isAlgebraic_qExpFunctionFieldC
-- name    : ModularCurve.exists_eq_algebraMap_of_isAlgebraic_qExpFunctionFieldC
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/f4a6a549-4e2c-5ce8-a44d-c94fbe870068
-- title:
--   ℚ is algebraically closed in the q-expansion field
-- statement:
--   Let $\Gamma$ be an arbitrary subgroup of $\mathrm{SL}_2(\mathbb{Z})$, and let `qExpFunctionFieldC ℚ Γ` be the intermediate field of the field of formal Laurent series $\mathbb{Q}((q))$ over $\mathbb{Q}$ obtained by adjoining to $\mathbb{Q}$ the set `intFormRatiosC ℚ Γ` of those Laurent series $x$ for which there exist an integer $k$, two modular forms $f,g$ of weight $k$ for the image of $\Gamma$ in $\mathrm{GL}_2(\mathbb{R})$, and two power series $pf, pg$ with integer coefficients such that `IsIntegralQExp f pf` and `IsIntegralQExp g pg` hold, the Laurent series `intSeriesC ℚ pg` is nonzero, and $x =$ `intSeriesC ℚ pf` $/$ `intSeriesC ℚ pg`. The assertion is that for every element $x$ of this intermediate field which is algebraic over $\mathbb{Q}$ there is a rational number $c$ with $x$ equal to the image of $c$ under the structure map $\mathbb{Q} \to$ `qExpFunctionFieldC ℚ Γ`; that is, $\mathbb{Q}$ is algebraically closed inside this field of $q$-expansion ratios.
--
--   This is the statement that the field of ratios of integral $q$-expansions of modular forms on $\Gamma$ contains no algebraic numbers beyond the rationals, i.e. that the extension of $\mathbb{Q}$ it defines is regular at the level of constants; no property of modular forms enters. It is used in the analysis of modular curves and their models, for instance when identifying constant fields of function fields and when base-changing the function field along a number field or an algebraic closure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_eq_algebraMap_of_isAlgebraic_qExpFunctionFieldC.lean

import Mathlib
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open ModularCurve

theorem ModularCurve.exists_eq_algebraMap_of_isAlgebraic_qExpFunctionFieldC
    (Γ : Subgroup SL(2, ℤ)) (x : ↥(qExpFunctionFieldC ℚ Γ)) (hx : IsAlgebraic ℚ x) :
    ∃ c : ℚ, x = algebraMap ℚ ↥(qExpFunctionFieldC ℚ Γ) c := by sorry

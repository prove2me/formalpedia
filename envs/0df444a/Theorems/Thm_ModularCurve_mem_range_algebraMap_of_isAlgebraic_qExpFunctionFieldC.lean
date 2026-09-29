-- Prove2me | Theorems.Thm_ModularCurve_mem_range_algebraMap_of_isAlgebraic_qExpFunctionFieldC
-- name    : ModularCurve.mem_range_algebraMap_of_isAlgebraic_qExpFunctionFieldC
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/43af9402-5d64-5e6c-9c5f-28ae70aa60d1
-- title:
--   κ is algebraically closed in the q-expansion function field
-- statement:
--   Let $\kappa$ be a field and $\Gamma$ a subgroup of $\mathrm{SL}_2(\mathbb{Z})$. Consider the intermediate field $\mathrm{qExpFunctionFieldC}\,\kappa\,\Gamma$ of the Laurent series field $\kappa((q))$ over $\kappa$, namely the subfield generated over $\kappa$ by the set [`ModularCurve.intFormRatiosC`](def/ModularCurve_X1.html#L83) of all quotients $\mathrm{intSeriesC}\,\kappa\,p_f/\mathrm{intSeriesC}\,\kappa\,p_g$, where $k$ is an integer, $f$ and $g$ are modular forms of weight $k$ on the image of $\Gamma$ in $\mathrm{GL}_2(\mathbb{R})$, $p_f,p_g$ are power series with integer coefficients that are integral $q$-expansions of $f$ and $g$ respectively (the predicate `IsIntegralQExp`), and the series $\mathrm{intSeriesC}\,\kappa\,p_g$ obtained from $p_g$ by passing its coefficients to $\kappa$ is non-zero. The assertion is that for every element $y$ of this field which is algebraic over $\kappa$, $y$ lies in the range of the structure map $\kappa \to \mathrm{qExpFunctionFieldC}\,\kappa\,\Gamma$; that is, $\kappa$ is algebraically closed in the $q$-expansion function field, so $\kappa$ is its exact constant field.
--
--   This says that $\kappa$ is the full constant field of the $q$-expansion function field of the modular curve attached to $\Gamma$ over $\kappa$, the condition under which this field behaves as the function field of a geometrically relevant curve over $\kappa$ and under which constant field extensions behave as expected. It is invoked when integral models and differentials on the modular curve are analysed, for instance in the construction of Kähler differentials from integral $q$-expansions of cusp forms and in the study of good points of two-chart integral models.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_mem_range_algebraMap_of_isAlgebraic_qExpFunctionFieldC.lean

import Mathlib
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.mem_range_algebraMap_of_isAlgebraic_qExpFunctionFieldC
    (κ : Type*) [Field κ] (Γ : Subgroup SL(2, ℤ))
    (y : ↥(ModularCurve.qExpFunctionFieldC κ Γ)) (hy : IsAlgebraic κ y) :
    y ∈ (algebraMap κ ↥(ModularCurve.qExpFunctionFieldC κ Γ)).range := by sorry

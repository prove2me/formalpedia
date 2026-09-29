-- Prove2me | Theorems.Thm_ModularCurve_exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange_qExpFunctionFieldC_of_T_mem
-- name    : ModularCurve.exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange_qExpFunctionFieldC_of_T_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/f63f1e25-7d3e-5e9b-a87a-3c7938f9a13e
-- title:
--   Elements of ℂ· F(Γ) are ratios of modular forms
-- statement:
--   Let $\Gamma$ be a subgroup of $\mathrm{SL}_2(\mathbb{Z})$ containing the translation matrix $T$ (no finite-index hypothesis is imposed), and let $x$ be a Laurent series over $\mathbb{C}$. Assume $x$ lies in [`ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ Γ)`](def/ModularCurve_LaurentCoeff.html#L103), that is, in the intermediate field of $\mathbb{C}((q))$ generated over $\mathbb{C}$ by the coefficientwise image under $\mathbb{Q} \to \mathbb{C}$ of the intermediate field `qExpFunctionFieldC ℚ Γ` of $\mathbb{Q}((q))$, the latter being generated over $\mathbb{Q}$ by the set of quotients `intSeriesC ℚ pf / intSeriesC ℚ pg` in which $k$ is an integer, $f$ and $g$ are modular forms of weight $k$ for $\Gamma$ (regarded inside $\mathrm{GL}_2(\mathbb{R})$), $pf$ and $pg$ are power series over $\mathbb{Z}$ satisfying `IsIntegralQExp f pf` and `IsIntegralQExp g pg`, and `intSeriesC ℚ pg ≠ 0`. The conclusion is that there are an integer $k$ and modular forms $g, h$ of weight $k$ for $\Gamma$ with $h \neq 0$ such that, in $\mathbb{C}((q))$, the product of $x$ with the period-$1$ $q$-expansion of $h$ equals the period-$1$ $q$-expansion of $g$.
--
--   This identifies the field of $q$-expansions of level $\Gamma$ with the field of $q$-expansions of ratios $g/h$ of two modular forms of a single weight on $\Gamma$; the hypothesis $T \in \Gamma$ is what makes period-$1$ $q$-expansions multiplicative. It is used in the analysis of the Galois action on points of modular curves, in particular in the results describing how algebra automorphisms and complex conjugation act on points via $q$-expansions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange_qExpFunctionFieldC_of_T_mem.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange_qExpFunctionFieldC_of_T_mem
    (Γ : Subgroup SL(2, ℤ)) (hT : ModularGroup.T ∈ Γ) (x : LaurentSeries ℂ)
    (hx : x ∈ ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ Γ)) :
    ∃ (k : ℤ) (g h : ModularForm Γ k), h ≠ 0 ∧
      x * ((UpperHalfPlane.qExpansion 1 (h : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
        ((UpperHalfPlane.qExpansion 1 (g : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) := by sorry

-- Prove2me | Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index
-- name    : ModularCurve.finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/4dd51e11-6963-58d5-8ed3-5d91243e5e6c
-- title:
--   Degree over L(j) bounded by the index of Γ'
-- statement:
--   Let $L$ be a field equipped with a $\mathbb{Q}$-algebra structure, let $\Gamma\le\mathrm{SL}_2(\mathbb{Z})$ be a subgroup of finite index containing the translation matrix `ModularGroup.T`, and let $\Gamma'\le\mathrm{SL}_2(\mathbb{Z})$ be a subgroup with $\Gamma\le\Gamma'$ such that every $\gamma\in\Gamma'$ satisfies $\gamma\in\Gamma$ or $-\gamma\in\Gamma$. Write $F_0=$ [`ModularCurve.qExpFunctionFieldC ℚ Γ`](def/ModularCurve_X1.html#L101) for the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by all quotients `intSeriesC ℚ pf / intSeriesC ℚ pg`, where for some weight $k$ there are modular forms $f,g$ of weight $k$ for the image of $\Gamma$ in $\mathrm{GL}_2(\mathbb{R})$ and integral power series $pf,pg$ with `IsIntegralQExp f pf`, `IsIntegralQExp g pg` and `intSeriesC ℚ pg ≠ 0`, and write $F=$ [`ModularCurve.laurentBaseChange L F₀`](def/ModularCurve_LaurentCoeff.html#L103) for the subfield of $L((q))$ generated over $L$ by the image of $F_0$ under the coefficientwise map $\mathbb{Q}((q))\to L((q))$ induced by $\mathbb{Q}\to L$. Let $y\in F$ be an element whose underlying Laurent series is [`ModularCurve.jqModC L`](def/ModularCurve_JqCoeff.html#L15), namely $q^{-1}$ times the image over $L$ of the integral power series [`ModularCurve.jNum`](def/ModularCurve_X0.html#L142) $=E_4^3\cdot$ `dedekindEtaUnitInv`. Then the $L(y)$-dimension of $F$, where $L(y)$ denotes the subfield of $F$ generated over $L$ by $y$, is at most the index of $\Gamma'$ in $\mathrm{SL}_2(\mathbb{Z})$. The conclusion is an inequality on `Module.finrank`, so it asserts a degree bound rather than finiteness of the extension.
--
--   This is the classical upper bound for the degree of the field of modular functions of level $\Gamma$ over the $j$-line, in the form $[F:L(j)]\le[\mathrm{SL}_2(\mathbb{Z}):\Gamma']$ for any $\Gamma'$ between $\Gamma$ and $\{\pm1\}\Gamma$, stated for the $q$-expansion model of the function field base changed to an arbitrary field $L$ of characteristic zero. It is used in the comparison of the generic and special degrees of modular curves over the $j$-line, and is invoked in the treatment of $X_1$, $X_0$ and full-level models, for instance in the ramification computation at complex places and in the finite-dimensionality statements for $\Gamma_H$ levels.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index
    (L : Type*) [Field L] [Algebra ℚ L]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex]
    (hT : ModularGroup.T ∈ Γ)
    (Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (hΓ' : Γ ≤ Γ')
    (hneg : ∀ γ ∈ Γ', γ ∈ Γ ∨ -γ ∈ Γ)
    (y : ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ))
    (hy : (y : LaurentSeries L) = ModularCurve.jqModC L) :
    Module.finrank
        (IntermediateField.adjoin L
          ({y} : Set (ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ))))
        (ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ)) ≤ Γ'.index := by sorry

-- Prove2me | Theorems.Thm_ModularCurve_exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange_qExpFunctionFieldC
-- name    : ModularCurve.exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange_qExpFunctionFieldC
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/33ba6941-ae96-5a37-b6ef-2d875c317bd8
-- title:
--   Elements of the base-changed q-expansion field are ratios of forms
-- statement:
--   Let $\Gamma$ be a subgroup of $\mathrm{SL}_2(\mathbb{Z})$ of finite index containing the translation matrix $T = \begin{pmatrix}1&1\\0&1\end{pmatrix}$, and let $x$ be a Laurent series over $\mathbb{C}$. Assume $x$ lies in [`ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ Γ)`](def/ModularCurve_LaurentCoeff.html#L103), that is, in the intermediate field of $\mathbb{C}((q))$ generated over $\mathbb{C}$ by the image of [`ModularCurve.qExpFunctionFieldC ℚ Γ`](def/ModularCurve_X1.html#L101) under the coefficientwise map $\mathbb{Q}((q)) \to \mathbb{C}((q))$ induced by $\mathbb{Q} \to \mathbb{C}$; here `qExpFunctionFieldC ℚ Γ` is the intermediate field of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the set `intFormRatiosC ℚ Γ` of quotients $\mathrm{intSeriesC}\,\mathbb{Q}\,p_f / \mathrm{intSeriesC}\,\mathbb{Q}\,p_g$, taken over all $k \in \mathbb{Z}$, all modular forms $f, g$ of weight $k$ for the image of $\Gamma$ in $\mathrm{GL}_2(\mathbb{R})$, and all integral power series $p_f, p_g$ satisfying the predicate `IsIntegralQExp` relative to $f$ and to $g$ respectively, subject to $\mathrm{intSeriesC}\,\mathbb{Q}\,p_g \neq 0$. The conclusion is that there exist a weight $k \in \mathbb{Z}$ and modular forms $g, h$ of weight $k$ for $\Gamma$ (viewed as a subgroup of $\mathrm{GL}_2(\mathbb{R})$) with $h \neq 0$ such that, in $\mathbb{C}((q))$, the product of $x$ with the $q$-expansion of $h$ of period $1$ equals the $q$-expansion of $g$ of period $1$, both expansions being coerced from power series to Laurent series.
--
--   This is the analytic description of the function field of the modular curve of level $\Gamma$: every element of $\mathbb{C}\cdot\mathbb{Q}(X(\Gamma))$, realised inside $\mathbb{C}((q))$, is the ratio of the $q$-expansions of two modular forms of equal weight on $\Gamma$. It is the $\Gamma$-generic form of the corresponding statement for $\Gamma_0(N)$ and serves as a shared input for the weight-$2m$ criterion on $\Gamma_1(M)$ and for the identification of regular differentials on $X_1(M)$ with weight-$2$ cusp forms, being used in particular by the results on Abel–Jacobi maps and point realisation for $\Gamma_H$-level curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange_qExpFunctionFieldC.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane in

theorem ModularCurve.exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange_qExpFunctionFieldC
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (x : LaurentSeries ℂ)
    (hx : x ∈ ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ Γ)) :
    ∃ (k : ℤ) (g h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k), h ≠ 0 ∧
      x * ((qExpansion 1 (h : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
        ((qExpansion 1 (g : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) := by sorry

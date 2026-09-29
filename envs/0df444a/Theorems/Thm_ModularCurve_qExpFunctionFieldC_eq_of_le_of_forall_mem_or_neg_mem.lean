-- Prove2me | Theorems.Thm_ModularCurve_qExpFunctionFieldC_eq_of_le_of_forall_mem_or_neg_mem
-- name    : ModularCurve.qExpFunctionFieldC_eq_of_le_of_forall_mem_or_neg_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/a061d07b-304e-5e8d-9e75-e4cc83b18d44
-- title:
--   q-expansion function field depends only on ±Γ
-- statement:
--   Let $K$ be a field and let $\Gamma$ and $\Gamma'$ be subgroups of $\mathrm{SL}_2(\mathbb{Z})$ with $\Gamma' \le \Gamma$, such that the translation matrix $T = \begin{pmatrix}1&1\\0&1\end{pmatrix}$, in the form `ModularGroup.T`, lies in $\Gamma'$, and such that every $\gamma \in \Gamma$ satisfies $\gamma \in \Gamma'$ or $-\gamma \in \Gamma'$. Then the two intermediate fields [`ModularCurve.qExpFunctionFieldC K Γ'`](def/ModularCurve_X1.html#L101) and [`ModularCurve.qExpFunctionFieldC K Γ`](def/ModularCurve_X1.html#L101) of the Laurent series field `LaurentSeries K` coincide. Here, for a subgroup $\Delta \le \mathrm{SL}_2(\mathbb{Z})$, [`ModularCurve.qExpFunctionFieldC K Δ`](def/ModularCurve_X1.html#L101) is the intermediate field obtained by adjoining to $K$ inside `LaurentSeries K` the set [`ModularCurve.intFormRatiosC K Δ`](def/ModularCurve_X1.html#L83) of all elements of the shape $\mathrm{intSeriesC}\,K\,p_f / \mathrm{intSeriesC}\,K\,p_g$, where $k \in \mathbb{Z}$, $f$ and $g$ are modular forms of weight $k$ for the image of $\Delta$ in $\mathrm{GL}_2(\mathbb{R})$, and $p_f, p_g \in \mathbb{Z}[[q]]$ are power series with integral coefficients satisfying the predicates [`ModularCurve.IsIntegralQExp f pf`](def/ModularCurve_X1.html#L37) and [`ModularCurve.IsIntegralQExp g pg`](def/ModularCurve_X1.html#L37) (recording that $p_f$, $p_g$ are integral $q$-expansions of $f$, $g$), subject to $\mathrm{intSeriesC}\,K\,p_g \ne 0$, where [`ModularCurve.intSeriesC K`](def/ModularCurve_X1.html#L69) carries an integral power series to the associated Laurent series over $K$.
--
--   This is the $q$-expansion-theoretic form, over an arbitrary coefficient field, of the classical fact that the function field of a modular curve depends only on the image of the group in $\mathrm{PSL}_2(\mathbb{Z})$, i.e. that $X(\Gamma) = X(\pm\Gamma)$. It is used in the treatment of separability of modular function fields in characteristic $2$ and $3$ at full level, where a group and its extension by $-1$ must be interchanged freely.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_qExpFunctionFieldC_eq_of_le_of_forall_mem_or_neg_mem.lean

import Mathlib
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.qExpFunctionFieldC_eq_of_le_of_forall_mem_or_neg_mem
    (K : Type*) [Field K] {Γ Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)} (hle : Γ' ≤ Γ)
    (hT : ModularGroup.T ∈ Γ') (hpm : ∀ γ ∈ Γ, γ ∈ Γ' ∨ -γ ∈ Γ') :
    ModularCurve.qExpFunctionFieldC K Γ' = ModularCurve.qExpFunctionFieldC K Γ := by sorry

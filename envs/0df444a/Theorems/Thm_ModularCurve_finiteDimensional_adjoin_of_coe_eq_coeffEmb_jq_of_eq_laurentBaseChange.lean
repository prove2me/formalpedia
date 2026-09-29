-- Prove2me | Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
-- name    : ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/79101f58-dc2f-50c9-8ae2-d1002a5afd51
-- title:
--   K is finite over L(j) for the q-expansion field
-- statement:
--   Let $\Gamma$ be a subgroup of finite index in $\mathrm{SL}_2(\mathbb{Z})$ containing the translation matrix $T$, and let $L$ be a field of characteristic zero. Write $F_0 =$ [`ModularCurve.qExpFunctionFieldC ℚ Γ`](def/ModularCurve_X1.html#L101) for the intermediate field of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by all quotients $\mathrm{intSeriesC}\,\mathbb{Q}\,p_f / \mathrm{intSeriesC}\,\mathbb{Q}\,p_g$, where $f,g$ are modular forms of some weight $k$ for the image of $\Gamma$ in $\mathrm{GL}_2(\mathbb{R})$ whose $q$-expansions are given by integral power series $p_f, p_g$ with the denominator series nonzero. Let $K$ be an intermediate field of $L((q))$ over $L$ assumed equal to [`ModularCurve.laurentBaseChange L F₀`](def/ModularCurve_LaurentCoeff.html#L103), i.e. to the field generated over $L$ by the image of $F_0$ under the coefficientwise map $\mathbb{Q}((q)) \to L((q))$ induced by $\mathbb{Q} \to L$. Let $j \in K$ be an element whose underlying Laurent series is the image under that coefficientwise map of [`ModularCurve.jq`](def/ModularCurve_X0.html#L157), namely $q^{-1}$ times the power series $\mathrm{jNumQ}$ over $\mathbb{Q}$. Then $K$ is a finite-dimensional vector space over the subfield $L(j) =$ `IntermediateField.adjoin L {j}`.
--
--   This is the classical finiteness of the field of modular functions attached to $\Gamma$ over the rational function field in $j$, here in the form $[K : L(j)] < \infty$ for the $L$-compositum of the $q$-expansion function field of $\Gamma$. It is the version of that finiteness pinned to the explicit generator $j$ and keyed to a hypothesis $K = \mathrm{laurentBaseChange}\,L\,(\ldots)$, so that it applies directly to the function fields of the modular curves used later in the construction of models and of Hecke correspondences.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange.lean

import Mathlib
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ))
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) :
    FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K := by sorry

-- Prove2me | Theorems.Thm_ModularCurve_ord_le_three_and_ord_sub_le_two_and_ord_sub_le_one_laurentBaseChange_qExpFunctionFieldC_algebraicClosure
-- name    : ModularCurve.ord_le_three_and_ord_sub_le_two_and_ord_sub_le_one_laurentBaseChange_qExpFunctionFieldC_algebraicClosure
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/9f862dcf-5606-58ad-a4b8-68f7df9191f0
-- title:
--   Ramification bounds for j on X(Γ) over ℚ̄
-- statement:
--   Fix a positive integer $M$ and a subgroup $\Gamma \le \mathrm{SL}_2(\mathbb{Z})$ containing $\Gamma_1(M)$. Let $F_0 =$ [`ModularCurve.qExpFunctionFieldC ℚ Γ`](def/ModularCurve_X1.html#L101) be the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by all quotients $\mathrm{intSeriesC}\,\mathbb{Q}\,p_f / \mathrm{intSeriesC}\,\mathbb{Q}\,p_g$, where $f,g$ are modular forms of one and the same weight $k$ on $\Gamma$ (viewed in $\mathrm{GL}_2(\mathbb{R})$) whose $q$-expansions are given by integral power series $p_f,p_g$ with the series attached to $p_g$ non-zero; and let $F =$ [`ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) F₀`](def/ModularCurve_LaurentCoeff.html#L103) be the subfield of $\overline{\mathbb{Q}}((q))$ generated over $\overline{\mathbb{Q}}$ by the image of $F_0$ under the coefficientwise embedding induced by $\mathbb{Q} \hookrightarrow \overline{\mathbb{Q}}$. Let $y \in F$ be an element whose underlying Laurent series is [`ModularCurve.jqModC`](def/ModularCurve_JqCoeff.html#L15), namely $q^{-1}$ times the image in $\overline{\mathbb{Q}}[[q]]$ of the integral power series $\mathrm{eisenstein4}^3 \cdot \mathrm{dedekindEtaUnitInv}$, i.e. the $q$-expansion of the modular invariant $j$. Let $P$ be a place of $F$ over $\overline{\mathbb{Q}}$, that is, a valuation subring of $F$ containing $\overline{\mathbb{Q}}$, distinct from $F$ and a principal ideal ring, with $\mathrm{ord}_P$ the associated normalised integer valuation. Then $\mathrm{ord}_P(y) \le 3$, $\mathrm{ord}_P(y - 1728) \le 2$, and $\mathrm{ord}_P(y - a) \le 1$ for every $a \in \overline{\mathbb{Q}}$ with $a \ne 0$ and $a \ne 1728$.
--
--   This is the classical bound on the ramification indices of the covering $j \colon X(\Gamma) \to X(1)$, which are at most $3$ above $j = 0$, at most $2$ above $j = 1728$ and at most $1$ above any other finite value of $j$, here in the $q$-expansion model of the function field over $\overline{\mathbb{Q}}$ rather than over $\mathbb{C}$. It is used in the computation of ramification indices along the inclusion of function fields for the curves $X_H$ of level $H$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ord_le_three_and_ord_sub_le_two_and_ord_sub_le_one_laurentBaseChange_qExpFunctionFieldC_algebraicClosure.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.ord_le_three_and_ord_sub_le_two_and_ord_sub_le_one_laurentBaseChange_qExpFunctionFieldC_algebraicClosure
    (M : ℕ) [NeZero M] (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (hΓ : CongruenceSubgroup.Gamma1 M ≤ Γ)
    (y : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ))
    (hy : (y : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.jqModC (AlgebraicClosure ℚ))
    (P : AlgebraicCurve.Place (AlgebraicClosure ℚ) (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ))) :
    P.ord y ≤ 3 ∧
    P.ord (y - 1728) ≤ 2 ∧
    (∀ a : AlgebraicClosure ℚ, a ≠ 0 → a ≠ 1728 →
      P.ord (y - algebraMap (AlgebraicClosure ℚ) (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) a) ≤ 1) := by sorry

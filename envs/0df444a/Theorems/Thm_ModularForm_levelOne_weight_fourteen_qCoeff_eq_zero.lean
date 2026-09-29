-- Prove2me | Theorems.Thm_ModularForm_levelOne_weight_fourteen_qCoeff_eq_zero
-- name    : ModularForm.levelOne_weight_fourteen_qCoeff_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/9f8f9c84-02ba-5a58-91a7-f8bfab8c6640
-- title:
--   Level-one weight-14 forms with vanishing constant term are zero
-- statement:
--   Let $Z$ be a modular form of weight $14$ for the full modular group $\mathrm{SL}_2(\mathbb{Z})$ (the group denoted $\mathcal{SL}$ in the `MatrixGroups` scoped notation). For a function $f$ on the upper half-plane and $n \in \mathbb{N}$, write $\mathrm{qCoeff}\,f\,n$ for the $n$-th coefficient of the $q$-expansion of $f$ of width $1$, that is, the coefficient of index $n$ in `qExpansion 1 f`. Assume that the constant term vanishes, $\mathrm{qCoeff}\,Z\,0 = 0$, where $Z$ is viewed through its underlying function on the upper half-plane. The conclusion is that $\mathrm{qCoeff}\,Z\,n = 0$ for every natural number $n$: all coefficients of the $q$-expansion of $Z$ vanish. Equivalently, a level-one modular form of weight $14$ whose constant term is zero has identically zero $q$-expansion; the statement is phrased coefficientwise rather than as the vanishing of $Z$ itself as an element of the space of modular forms.
--
--   This records the absence of nonzero cusp forms of weight $14$ and level one, in the coefficientwise form needed downstream. It is used in the congruence arguments for $q$-coefficients of cusp forms attached to the discriminant and in the divisibility statement [`ModularForm.dvd_succ_mul_qCoeff_zero_of_dvd_qCoeff`](thm.html#ModularForm.dvd_succ_mul_qCoeff_zero_of_dvd_qCoeff).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_levelOne_weight_fourteen_qCoeff_eq_zero.lean

import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups

theorem ModularForm.levelOne_weight_fourteen_qCoeff_eq_zero (Z : ModularForm 𝒮ℒ 14) (h0 : ModularFormClass.qCoeff ⇑Z 0 = 0) : ∀ n : ℕ, ModularFormClass.qCoeff ⇑Z n = 0 := by sorry

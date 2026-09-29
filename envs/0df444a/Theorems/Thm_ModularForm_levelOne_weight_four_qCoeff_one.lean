-- Prove2me | Theorems.Thm_ModularForm_levelOne_weight_four_qCoeff_one
-- name    : ModularForm.levelOne_weight_four_qCoeff_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/d72ee19f-da51-59b5-8b15-aad02c02caa0
-- title:
--   Weight four level one: a₁ = 240 a₀
-- statement:
--   Let $Y$ be a modular form of weight $4$ for the full modular group $\mathrm{SL}_2(\mathbb{Z})$, i.e. an element of `ModularForm 𝒮ℒ 4`. For a function $f$ on the upper half-plane, [`ModularFormClass.qCoeff f n`](def/FLTPrelim_Modularity.html#L19) denotes the $n$-th coefficient of the $q$-expansion of $f$ taken with respect to period $1$, that is, the coefficient of $q^n$ in `qExpansion 1 f`. The theorem asserts that the first two such coefficients of (the underlying function of) $Y$ are related by
--   $$\mathrm{qCoeff}\,Y\,1 = 240 \cdot \mathrm{qCoeff}\,Y\,0,$$
--   an identity in $\mathbb{C}$. No further hypotheses are imposed: the statement holds for every weight-four level-one form, including the zero form, and in particular pins down the linear coefficient of such a form in terms of its constant term.
--
--   This is the coefficient identity expressing that the space of level-one modular forms of weight $4$ is spanned by the Eisenstein series $E_4 = 1 + 240q + \cdots$, so that any such form is a scalar multiple of $E_4$. It is used in the project wherever weight-four level-one forms occur, for instance in the divisibility estimate [`CuspForm.dvd_240_mul_qCoeff_one_sq_of_qCoeff_congr_sigmaPrimeTo`](thm.html#CuspForm.dvd_240_mul_qCoeff_one_sq_of_qCoeff_congr_sigmaPrimeTo) and in the bounds on analytic orders of vanishing on modular curves appearing in [`ModularCurve.analyticOrderAt_le_of_isIntegral_adjoin_coeffEmb_jq`](thm.html#ModularCurve.analyticOrderAt_le_of_isIntegral_adjoin_coeffEmb_jq) and its variant for powers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_levelOne_weight_four_qCoeff_one.lean

import Definitions.Def_FLTPrelim_Modularity
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups

theorem ModularForm.levelOne_weight_four_qCoeff_one (Y : ModularForm 𝒮ℒ 4) : ModularFormClass.qCoeff ⇑Y 1 = 240 * ModularFormClass.qCoeff ⇑Y 0 := by sorry

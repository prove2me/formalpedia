-- Prove2me | Theorems.Thm_ModularForm_levelOne_eq_zero_of_lt_order_qExpansion
-- name    : ModularForm.levelOne_eq_zero_of_lt_order_qExpansion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/e1585de7-1d2c-5b27-b930-e63ef4b550b7
-- title:
--   Level-one vanishing from q-expansion order at width M
-- statement:
--   Let $M$ be a natural number with $0 < M$, let $k$ be an integer, and let $F$ be a modular form of weight $k$ for the full modular group $\mathcal{SL}$, i.e. an element of `ModularForm 𝒮ℒ k`. Consider the power series `qExpansion (M : ℝ) F`, the $q$-expansion of $F$ computed with respect to the width $M$, so in the variable $q_M = e^{2\pi i \tau / M}$. The hypothesis is that the natural number $M \cdot (\mathrm{k.toNat} / 12)$, where `k.toNat` is $\max(k,0)$ and the division is truncated division of natural numbers, is strictly smaller, as an element of $\mathbb{N}\cup\{\infty\}$, than the order of that power series (the order being $\infty$ when the series vanishes). The conclusion is that $F = 0$. Thus a level-one form of weight $k$ whose width-$M$ expansion vanishes to order exceeding $M\lfloor k/12\rfloor$ (with the convention that negative weights give the bound $0$) is identically zero.
--
--   This is the Sturm bound in level one, stated for an expansion variable of arbitrary width $M$ rather than only for the standard width $1$. It is the shape in which the level-one bound is applied to forms whose natural expansion parameter is $q_M$, such as norms $\prod_\gamma f\,|_k\,\gamma$ of forms on a finite-index subgroup; it is cited by [`ModularForm.eq_zero_of_lt_order_qExpansion_of_isArithmetic`](thm.html#ModularForm.eq_zero_of_lt_order_qExpansion_of_isArithmetic).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_levelOne_eq_zero_of_lt_order_qExpansion.lean

import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane
open scoped MatrixGroups Manifold

theorem ModularForm.levelOne_eq_zero_of_lt_order_qExpansion (M : ℕ) (hM : 0 < M) {k : ℤ} (F : ModularForm 𝒮ℒ k) (h : ((M * (k.toNat / 12) : ℕ) : ℕ∞) < (qExpansion (M : ℝ) F).order) : F = 0 := by sorry

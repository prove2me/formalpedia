-- Prove2me | Theorems.Thm_Matrix_SpecialLinearGroup_trace_sq_le_four_of_isOfFinOrder
-- name    : Matrix.SpecialLinearGroup.trace_sq_le_four_of_isOfFinOrder
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/5c88dde7-8432-5e2a-abd5-7fcdf6199099
-- title:
--   Finite-order elements of SL₂(ℤ) have trace squared at most 4
-- statement:
--   Let $\gamma$ be an element of $\mathrm{SL}(2,\mathbb{Z})$, the group of $2\times 2$ integer matrices of determinant $1$ (in the `MatrixGroups` notation `SL(2, ℤ)`), and suppose $\gamma$ is of finite order, i.e. `IsOfFinOrder γ` holds, so that $\gamma^n = 1$ for some $n \ge 1$. The conclusion is that the square of the trace of the underlying integer matrix of $\gamma$, an element of $\mathbb{Z}$, satisfies $(\operatorname{tr}\gamma)^2 \le 4$. Equivalently $\operatorname{tr}\gamma \in \{0,\pm 1,\pm 2\}$, although the statement is given in the inequality form and asserts nothing about which traces actually occur, nor any converse assigning orders to the admissible traces.
--
--   This is the elementary trace bound for elliptic and central elements of the modular group: a finite-order element of $\mathrm{SL}_2(\mathbb{Z})$ has trace $0$, $\pm 1$ or $\pm 2$. It is used in [`CohCarrier.exists_linearMap_baseChange_parabolicHoms_gammaH_bot_range_eq_parabolicHoms_of_four_le`](thm.html#CohCarrier.exists_linearMap_baseChange_parabolicHoms_gammaH_bot_range_eq_parabolicHoms_of_four_le), where torsion in a congruence subgroup must be excluded.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_SpecialLinearGroup_trace_sq_le_four_of_isOfFinOrder.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem Matrix.SpecialLinearGroup.trace_sq_le_four_of_isOfFinOrder (γ : SL(2, ℤ)) (h : IsOfFinOrder γ) :
    (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 ≤ 4 := by sorry

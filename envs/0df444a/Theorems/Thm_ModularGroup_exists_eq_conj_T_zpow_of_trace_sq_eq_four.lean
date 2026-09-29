-- Prove2me | Theorems.Thm_ModularGroup_exists_eq_conj_T_zpow_of_trace_sq_eq_four
-- name    : ModularGroup.exists_eq_conj_T_zpow_of_trace_sq_eq_four
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/6b721e9a-dc95-5f8f-86c9-2be3af8e0bc2
-- title:
--   Trace-±2 elements of SL₂(ℤ) are ±δ T^hδ⁻¹
-- statement:
--   Let $\gamma$ be an element of $SL(2,\mathbb{Z})$, the group of $2\times 2$ integer matrices of determinant $1$, and suppose that the square of the trace of the underlying matrix of $\gamma$ equals $4$, i.e. $(\operatorname{tr}\gamma)^2 = 4$, so that $\operatorname{tr}\gamma = 2$ or $\operatorname{tr}\gamma = -2$. The assertion is that there exist elements $\varepsilon,\delta \in SL(2,\mathbb{Z})$ and an integer $h$ such that $\varepsilon$ is either the identity matrix or its negative, and $\gamma = \varepsilon\,(\delta\, T^{h}\, \delta^{-1})$, where $T$ denotes the Mathlib matrix $\begin{pmatrix}1&1\\0&1\end{pmatrix}$ in $SL(2,\mathbb{Z})$ and $T^h$ is its integer power $\begin{pmatrix}1&h\\0&1\end{pmatrix}$. Thus every element of trace $\pm 2$, including $\pm 1$ themselves (the case $h = 0$), is a sign times a conjugate of a power of $T$. The sign $\varepsilon$, the conjugating element $\delta$ and the exponent $h$ are produced existentially, with no uniqueness or normalisation claimed.
--
--   This is the classification of elements of $SL_2(\mathbb{Z})$ with $(\operatorname{tr})^2 = 4$, equivalently the statement that the stabiliser of a cusp is conjugate to $\{\pm T^h : h \in \mathbb{Z}\}$. It is the group-theoretic input to the parabolicity of Eichler–Shimura period cocycles attached to cusp forms, and is used throughout the treatment of the cohomological carrier of modular symbols.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularGroup_exists_eq_conj_T_zpow_of_trace_sq_eq_four.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularGroup.exists_eq_conj_T_zpow_of_trace_sq_eq_four (γ : SL(2, ℤ))
    (hγ : ((γ : Matrix (Fin 2) (Fin 2) ℤ).trace) ^ 2 = 4) :
    ∃ (ε δ : SL(2, ℤ)) (h : ℤ), (ε = 1 ∨ ε = -1) ∧ γ = ε * (δ * ModularGroup.T ^ h * δ⁻¹) := by sorry

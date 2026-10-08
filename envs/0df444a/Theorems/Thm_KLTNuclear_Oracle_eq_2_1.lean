-- Prove2me | Theorems.Thm_KLTNuclear_Oracle_eq_2_1
-- name    : KLTNuclear.Oracle.eq_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:50:30.892206+00:00
-- url     : https://prove2.me/theorems/4b115c04-e413-47ef-80ee-d99d7e3a7dd0
-- title:
--   (2.1) — the subdifferential of the nuclear norm
-- statement:
--   Let $A$ be a real $m_1\times m_2$ matrix with singular value decomposition $A=\sum_{j=1}^r\sigma_ju_jv_j^\top$, where $\sigma_j>0$ and $u_1,\dots,u_r\in\mathbb R^{m_1}$, $v_1,\dots,v_r\in\mathbb R^{m_2}$ are orthonormal. Let $S_1=\operatorname{span}\{u_j\}$, $S_2=\operatorname{span}\{v_j\}$ (the support of $A$) and let $P_S$ denote the orthogonal projector onto $S$. A matrix $V$ is a subgradient of the nuclear norm $\|\cdot\|_1$ at $A$ if and only if it has the form
--   $$V=\sum_{j=1}^r u_jv_j^\top+P_{S_1^\perp}WP_{S_2^\perp}\quad\text{for some } W \text{ with } \|W\|_\infty\le 1,$$
--   where $\|W\|_\infty$ is the operator norm. That is,
--   $$\partial\|A\|_1=\Big\{\sum_{j=1}^r u_jv_j^\top+P_{S_1^\perp}WP_{S_2^\perp}:\ \|W\|_\infty\le1\Big\}.$$
--
--   This description of the subdifferential (Watson) is what turns the first-order optimality condition (2.6) into the inequality (2.8) in the proof of Theorem 1.
--
--   **Formalization Note** Subgradient means $\|A\|_1+\langle V,B-A\rangle\le\|B\|_1$ for all $B$. The SVD is given as data `S : SVD A r` (positive singular values, orthonormal singular vectors, in any order); $r=0$ covers $A=0$, where the statement says $\partial\|0\|_1$ is the unit operator-norm ball. $P_{S_1^\perp}WP_{S_2^\perp}$ is `normalProjection S W`.
-- source:
--   Koltchinskii, Lounici, Tsybakov, Nuclear-Norm Penalization and Optimal Rates for Noisy Low-Rank Matrix Completion, arXiv:1011.6256v4, p. 6, (2.1)

import Mathlib
import Definitions.Def_KLTNuclear_Oracle_Model

open MeasureTheory MatrixCompletion

namespace KLTNuclear.Oracle

/-- (2.1) (p. 6): the subdifferential of the nuclear norm at A with SVD
A = Σⱼ σⱼ uⱼ vⱼᵀ and support (S₁, S₂) is { Σⱼ uⱼ vⱼᵀ + P_{S₁⊥} W P_{S₂⊥} : ‖W‖∞ ≤ 1 }. -/
theorem eq_2_1 {m₁ m₂ r : ℕ} {A : RealMatrix m₁ m₂} (S : SVD A r) (V : RealMatrix m₁ m₂) :
    IsNuclearSubgradient A V ↔
      ∃ W : RealMatrix m₁ m₂, spectralNorm W ≤ 1 ∧ V = signMatrix S + normalProjection S W := by sorry

end KLTNuclear.Oracle

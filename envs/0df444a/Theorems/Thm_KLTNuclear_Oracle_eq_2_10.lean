-- Prove2me | Theorems.Thm_KLTNuclear_Oracle_eq_2_10
-- name    : KLTNuclear.Oracle.eq_2_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:50:50.091307+00:00
-- url     : https://prove2.me/theorems/1f82f15a-ac8c-41e4-8d8c-ec4e38150ca5
-- title:
--   (2.10) — $\|\sum_j u_jv_j^\top\|_\infty=1$ and $\langle\sum_j u_jv_j^\top,B\rangle=\langle\sum_j u_jv_j^\top,P_{S_1}BP_{S_2}\rangle$
-- statement:
--   Let $A=\sum_{j=1}^r\sigma_ju_jv_j^\top$ be a singular value decomposition of a real $m_1\times m_2$ matrix, with support $(S_1,S_2)$ and $P_{S_1}$, $P_{S_2}$ the orthogonal projectors onto $S_1$, $S_2$. Then
--
--   1. if $A\ne0$ (that is, $r\ge1$), $\big\|\sum_{j=1}^ru_jv_j^\top\big\|_\infty=1$ (operator norm);
--   2. for every $m_1\times m_2$ matrix $B$,
--   $$\Big\langle\sum_{j=1}^ru_jv_j^\top,B\Big\rangle=\Big\langle\sum_{j=1}^ru_jv_j^\top,P_{S_1}BP_{S_2}\Big\rangle .$$
--
--   In the proof of Theorem 1 these are applied with $B=\hat A^\lambda-A$ to bound the term $-\lambda\langle\sum_ju_jv_j^\top,\hat A^\lambda-A\rangle$ of (2.8).
--
--   **Formalization Note** The paper states the first fact without restriction; for $A=0$ the sum is empty and its norm is $0$, so the condition $r>0$ is added (it is the case the proof uses: for $A=0$ the term vanishes). The paper writes $B=\hat A^\lambda-A$; the second fact holds for every $B$ and is stated so.
-- source:
--   Koltchinskii, Lounici, Tsybakov, Nuclear-Norm Penalization and Optimal Rates for Noisy Low-Rank Matrix Completion, arXiv:1011.6256v4, p. 8, (2.10)

import Mathlib
import Definitions.Def_KLTNuclear_Oracle_Model

open MeasureTheory MatrixCompletion

namespace KLTNuclear.Oracle

/-- (2.10) (p. 8): for an SVD A = Σⱼ σⱼ uⱼ vⱼᵀ of a nonzero A (r > 0),
‖Σⱼ uⱼ vⱼᵀ‖∞ = 1 and ⟨Σⱼ uⱼ vⱼᵀ, B⟩ = ⟨Σⱼ uⱼ vⱼᵀ, P_{S₁} B P_{S₂}⟩ for every matrix B
(in the paper B = Â^λ − A). -/
theorem eq_2_10 {m₁ m₂ r : ℕ} {A : RealMatrix m₁ m₂} (S : SVD A r) :
    (0 < r → spectralNorm (signMatrix S) = 1) ∧
      ∀ B : RealMatrix m₁ m₂,
        matrixInner (signMatrix S) B = matrixInner (signMatrix S) (twoSidedSingularProjection S B) := by sorry

end KLTNuclear.Oracle

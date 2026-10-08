-- Prove2me | Theorems.Thm_KLTNuclear_RestrictedEigen_eq_2_21
-- name    : KLTNuclear.RestrictedEigen.eq_2_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:40:32.68983+00:00
-- url     : https://prove2.me/theorems/4ca2c550-f4b6-48c7-92e9-a8084339c99d
-- title:
--   (2.21) — ⟨M, B⟩ splits along 𝒫_A and 𝒫_A⊥ and is at most ‖M‖∞(‖𝒫_A B‖₁ + ‖𝒫_A⊥ B‖₁)
-- statement:
--   Let $A$ be an $m_1 \times m_2$ real matrix with support $(S_1, S_2)$, and let $\mathbf M$ and $B$ be any $m_1 \times m_2$ real matrices. Then
--   $$
--   \langle \mathbf M, B\rangle = \langle \mathbf M, \mathcal P_A(B)\rangle + \langle \mathbf M, \mathcal P_A^\perp(B)\rangle \le \|\mathbf M\|_\infty\big(\|\mathcal P_A(B)\|_1 + \|\mathcal P_A^\perp(B)\|_1\big),
--   $$
--   where $\|\cdot\|_\infty$ is the operator norm (largest singular value) and $\|\cdot\|_1$ the nuclear norm.
--
--   In the proof of Theorem 2 this is applied with $B = \hat A^\lambda - A$ and the noise matrix $\mathbf M$ of (2.2). It is the only place where the size of the noise enters the cone argument.
--
--   **Formalization Note** The page states the display for $B = \hat A^\lambda - A$; the Lean statement holds for every matrix $B$, of which the page's display is an instance. It is a consequence of trace duality (`matrix_trace_duality_inequality`).
-- source:
--   Koltchinskii, Lounici, Tsybakov, Nuclear-Norm Penalization and Optimal Rates for Noisy Low-Rank Matrix Completion, arXiv:1011.6256v4, p. 11, (2.21) (proof of Theorem 2)

import Mathlib
import Definitions.Def_matrix_completion_tangent

open MatrixCompletion

namespace KLTNuclear.RestrictedEigen

/-- (2.21), proof of Theorem 2, arXiv:1011.6256v4, p. 11: for a matrix `A` with SVD `S`
(support (S₁, S₂)), any matrix **M** and any matrix `B` (in the paper `B = Â^λ − A`),
⟨M, B⟩ = ⟨M, 𝒫_A(B)⟩ + ⟨M, 𝒫_A⊥(B)⟩ ≤ ‖M‖∞ (‖𝒫_A(B)‖₁ + ‖𝒫_A⊥(B)‖₁).
Formalization Note: the display is stated for an arbitrary matrix `B` in place of `Â^λ − A`;
the paper's instance is the special case. -/
theorem eq_2_21 {m₁ m₂ r : ℕ} {A : RealMatrix m₁ m₂} (S : SVD A r) (M B : RealMatrix m₁ m₂) :
    matrixInner M B = matrixInner M (tangentProjection S B) + matrixInner M (normalProjection S B) ∧
      matrixInner M B ≤
        spectralNorm M * (nuclearNorm (tangentProjection S B) + nuclearNorm (normalProjection S B)) := by sorry

end KLTNuclear.RestrictedEigen

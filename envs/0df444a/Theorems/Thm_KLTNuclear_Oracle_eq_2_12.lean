-- Prove2me | Theorems.Thm_KLTNuclear_Oracle_eq_2_12
-- name    : KLTNuclear.Oracle.eq_2_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:50:46.18222+00:00
-- url     : https://prove2.me/theorems/36ad0bd5-b850-4086-bb20-e03659ed676e
-- title:
--   (2.12)–(2.14) — $2|\langle M,B-A\rangle|\le\Lambda\|\mathcal P_A(B-A)\|_2+\Gamma\|P_{S_1^\perp}BP_{S_2^\perp}\|_1$ and $\Gamma\le2\|M\|_\infty$
-- statement:
--   Let $A=\sum_{j=1}^r\sigma_ju_jv_j^\top$ be a singular value decomposition of a real $m_1\times m_2$ matrix with support $(S_1,S_2)$, let $\mathcal P_A(N)=N-P_{S_1^\perp}NP_{S_2^\perp}$, and let $M$ and $B$ be any $m_1\times m_2$ matrices. Set
--   $$\Lambda=2\|\mathcal P_A(M)\|_2,\qquad\Gamma=2\|P_{S_1^\perp}MP_{S_2^\perp}\|_\infty,$$
--   with $\|\cdot\|_2$ the Frobenius norm and $\|\cdot\|_\infty$ the operator norm. Then
--   $$2|\langle M,B-A\rangle|\le\Lambda\|\mathcal P_A(B-A)\|_2+\Gamma\|P_{S_1^\perp}BP_{S_2^\perp}\|_1\le\Lambda\|B-A\|_2+\Gamma\|P_{S_1^\perp}BP_{S_2^\perp}\|_1,$$
--   and
--   $$\Gamma\le2\|M\|_\infty .$$
--
--   In the proof of Theorem 1 this is applied with $M=\mathbf M$ and $B=\hat A^\lambda$ to control the stochastic term of (2.11).
--
--   **Formalization Note** The paper states (2.12)–(2.14) for the random matrix $\mathbf M$ and $B=\hat A^\lambda$; they are deterministic facts about any matrices and are stated so. $\Lambda$ and $\Gamma$ are written out inline.
-- source:
--   Koltchinskii, Lounici, Tsybakov, Nuclear-Norm Penalization and Optimal Rates for Noisy Low-Rank Matrix Completion, arXiv:1011.6256v4, p. 9, (2.12), (2.13), (2.14)

import Mathlib
import Definitions.Def_KLTNuclear_Oracle_Model

open MeasureTheory MatrixCompletion

namespace KLTNuclear.Oracle

/-- (2.12)–(2.14) (p. 9), for an arbitrary matrix N in place of 𝐌 and B in place of Â^λ:
with Λ = 2‖𝒫_A(N)‖₂ and Γ = 2‖P_{S₁⊥} N P_{S₂⊥}‖∞ (2.13),
2|⟨N, B − A⟩| ≤ Λ‖𝒫_A(B − A)‖₂ + Γ‖P_{S₁⊥} B P_{S₂⊥}‖₁ ≤ Λ‖B − A‖₂ + Γ‖P_{S₁⊥} B P_{S₂⊥}‖₁,
and Γ ≤ 2‖N‖∞ (2.14). -/
theorem eq_2_12 {m₁ m₂ r : ℕ} {A : RealMatrix m₁ m₂} (S : SVD A r) (N B : RealMatrix m₁ m₂) :
    2 * |matrixInner N (B - A)| ≤
        2 * frobeniusNorm (tangentProjection S N) * frobeniusNorm (tangentProjection S (B - A)) +
          2 * spectralNorm (normalProjection S N) * nuclearNorm (normalProjection S B) ∧
      2 * frobeniusNorm (tangentProjection S N) * frobeniusNorm (tangentProjection S (B - A)) +
          2 * spectralNorm (normalProjection S N) * nuclearNorm (normalProjection S B) ≤
        2 * frobeniusNorm (tangentProjection S N) * frobeniusNorm (B - A) +
          2 * spectralNorm (normalProjection S N) * nuclearNorm (normalProjection S B) ∧
      2 * spectralNorm (normalProjection S N) ≤ 2 * spectralNorm N := by sorry

end KLTNuclear.Oracle

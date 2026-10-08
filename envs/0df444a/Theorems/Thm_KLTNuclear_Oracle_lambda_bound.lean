-- Prove2me | Theorems.Thm_KLTNuclear_Oracle_lambda_bound
-- name    : KLTNuclear.Oracle.lambda_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:50:44.59452+00:00
-- url     : https://prove2.me/theorems/a0b1c6ab-7354-486c-b391-ec70db5b1938
-- title:
--   (2.15) and $\Lambda\le2\sqrt{\operatorname{rank}(\mathcal P_A(M))}\|M\|_\infty\le2\sqrt{2\operatorname{rank}(A)}\|M\|_\infty\le\sqrt{2\operatorname{rank}(A)}\lambda$
-- statement:
--   Let $A=\sum_{j=1}^r\sigma_ju_jv_j^\top$ be a singular value decomposition of a real $m_1\times m_2$ matrix with support $(S_1,S_2)$, let $M$ be any $m_1\times m_2$ matrix, and let $\mathcal P_A(M)=M-P_{S_1^\perp}MP_{S_2^\perp}$ and $\Lambda=2\|\mathcal P_A(M)\|_2$. Then
--
--   1. (2.15) $\mathcal P_A(M)=P_{S_1^\perp}MP_{S_2}+P_{S_1}M$;
--   2. $\Lambda\le2\sqrt{\operatorname{rank}(\mathcal P_A(M))}\,\|M\|_\infty$;
--   3. $2\sqrt{\operatorname{rank}(\mathcal P_A(M))}\,\|M\|_\infty\le2\sqrt{2\operatorname{rank}(A)}\,\|M\|_\infty$;
--   4. for every $\lambda\ge2\|M\|_\infty$, $2\sqrt{2\operatorname{rank}(A)}\,\|M\|_\infty\le\sqrt{2\operatorname{rank}(A)}\,\lambda$.
--
--   Together: $\Lambda\le2\sqrt{\operatorname{rank}(\mathcal P_A(M))}\|M\|_\infty\le2\sqrt{2\operatorname{rank}(A)}\Delta\le\sqrt{2\operatorname{rank}(A)}\lambda$ with $\Delta=\|M\|_\infty$, which is the bound on $\Lambda$ used to pass from (2.17) to (2.5).
--
--   **Formalization Note** $P_{S_1^\perp}MP_{S_2}$ is written as $MP_{S_2}-P_{S_1}MP_{S_2}$ (`rightSingularProjection S M - twoSidedSingularProjection S M`). The paper states the chain for the random matrix $\mathbf M$; it holds for every $M$ and is stated so. Rank is Mathlib's `Matrix.rank`.
-- source:
--   Koltchinskii, Lounici, Tsybakov, Nuclear-Norm Penalization and Optimal Rates for Noisy Low-Rank Matrix Completion, arXiv:1011.6256v4, p. 9, (2.15) and the display following it

import Mathlib
import Definitions.Def_KLTNuclear_Oracle_Model

open MeasureTheory MatrixCompletion

namespace KLTNuclear.Oracle

/-- (2.15) and the bound on Λ = 2‖𝒫_A(N)‖₂ (p. 9), for an arbitrary matrix N in place of 𝐌:
𝒫_A(N) = P_{S₁⊥} N P_{S₂} + P_{S₁} N, and
Λ ≤ 2√(rank 𝒫_A(N)) ‖N‖∞ ≤ 2√(2 rank A) ‖N‖∞ ≤ √(2 rank A) λ when λ ≥ 2‖N‖∞. -/
theorem lambda_bound {m₁ m₂ r : ℕ} {A : RealMatrix m₁ m₂} (S : SVD A r) (N : RealMatrix m₁ m₂) :
    -- (2.15)
    tangentProjection S N =
        (rightSingularProjection S N - twoSidedSingularProjection S N) + leftSingularProjection S N ∧
      2 * frobeniusNorm (tangentProjection S N) ≤
        2 * Real.sqrt ((tangentProjection S N).rank : ℝ) * spectralNorm N ∧
      2 * Real.sqrt ((tangentProjection S N).rank : ℝ) * spectralNorm N ≤
        2 * Real.sqrt (2 * (A.rank : ℝ)) * spectralNorm N ∧
      ∀ lam : ℝ, 2 * spectralNorm N ≤ lam →
        2 * Real.sqrt (2 * (A.rank : ℝ)) * spectralNorm N ≤ Real.sqrt (2 * (A.rank : ℝ)) * lam := by sorry

end KLTNuclear.Oracle

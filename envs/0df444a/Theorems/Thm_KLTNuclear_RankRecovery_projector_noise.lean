-- Prove2me | Theorems.Thm_KLTNuclear_RankRecovery_projector_noise
-- name    : KLTNuclear.RankRecovery.projector_noise
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:48:33.154323+00:00
-- url     : https://prove2.me/theorems/639788c7-7c57-4473-b2b4-fd5ec997cc6f
-- title:
--   Proof of (5.3), p. 20 — $\|\mathcal P(\mathbf X-A_0)\|_2\le\sqrt r\|\mathbf M\|_\infty m_1m_2\le\sqrt r\lambda m_1m_2/2$
-- statement:
--   Consider the matrix completion data of the module `KLTNuclear.RankRecovery.Model` ($n,m_1,m_2\ge1$), a matrix $A_0$, the matrices $\mathbf X$ and $\mathbf M=\frac1n\sum_iY_iX_i-A_0/(m_1m_2)$, and $\lambda>0$ with $\lambda\ge2\|\mathbf M\|_\infty$. Let $\mathbf X=\sum_{k=1}^q\sigma_ku_kv_k^\top$ be a singular value decomposition with $\sigma_1\ge\dots\ge\sigma_q>0$, $r=\operatorname{rank}(A_0)$, and $\mathcal P$ the orthogonal projector onto the span of $u_kv_k^\top$, $k\le r$. Then
--
--   $$\|\mathcal P(\mathbf X-A_0)\|_2\le\sqrt r\,\|\mathbf M\|_\infty\,m_1m_2\le\sqrt r\,\frac{\lambda m_1m_2}{2}.$$
--
--   A projector onto a span of $r$ orthonormal rank-one matrices cannot capture more than $\sqrt r$ times the operator norm in Frobenius norm; applied to the noise $\mathbf X-A_0=m_1m_2\mathbf M$, this is the second half of the lower bound (5.3).
--
--   **Formalization Note** $\|\cdot\|_\infty$ is `spectralNorm` (the largest singular value), $\|\cdot\|_2$ is `frobeniusNorm`. The projector is `spanProjector` on the pairs with 0-based index $k<r$.
-- source:
--   Koltchinskii, Lounici, Tsybakov, Nuclear-Norm Penalization and Optimal Rates for Noisy Low-Rank Matrix Completion, arXiv:1011.6256v4, p. 20, proof of Theorem 8, (5.3) ('On the other hand, ‖𝒫(X − A0)‖2 ≤ √r‖M‖∞m1m2 ≤ √rλm1m2/2')

import Mathlib
import Definitions.Def_KLTNuclear_RankRecovery_Model

open MatrixCompletion

namespace KLTNuclear.RankRecovery

/-- Proof of (5.3) (p. 20): with `𝒫` the projector onto the span of the first `r = rank(A₀)`
pairs `u_k(𝐗) v_k(𝐗)ᵀ` of an SVD of `𝐗` with decreasing singular values,
`‖𝒫(𝐗 − A₀)‖₂ ≤ √r ‖𝐌‖∞ m₁m₂ ≤ √r λm₁m₂/2` when `λ ≥ 2‖𝐌‖∞`. -/
theorem projector_noise {m₁ m₂ n : ℕ} (hn : 0 < n) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (idx : Fin n → Fin m₁ × Fin m₂) (y : Fin n → ℝ) (A₀ : RealMatrix m₁ m₂)
    (lam : ℝ) (hlam : 0 < lam)
    (hM : 2 * spectralNorm (noiseMatrix idx y A₀) ≤ lam)
    (q : ℕ) (S : SVD (bigX idx y) q) (hS : Antitone S.sigma) :
    frobeniusNorm (spanProjector (fun k : {k : Fin q // k.val < A₀.rank} => S.u k.val)
        (fun k => S.v k.val) (bigX idx y - A₀)) ≤
        Real.sqrt A₀.rank * spectralNorm (noiseMatrix idx y A₀) * ((m₁ : ℝ) * m₂) ∧
      Real.sqrt A₀.rank * spectralNorm (noiseMatrix idx y A₀) * ((m₁ : ℝ) * m₂) ≤
        Real.sqrt A₀.rank * lam * ((m₁ : ℝ) * m₂) / 2 := by sorry

end KLTNuclear.RankRecovery

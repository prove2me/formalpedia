-- Prove2me | Theorems.Thm_KLTNuclear_RankRecovery_theorem_8
-- name    : KLTNuclear.RankRecovery.theorem_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:48:27.487658+00:00
-- url     : https://prove2.me/theorems/eeb03ed6-f3cd-4547-a899-1190c1ce3fbf
-- title:
--   Theorem 8 — the estimator $\hat A^{\lambda'}$ never overestimates rank$(A_0)$, recovers it above a singular-value gap, and obeys the lower bound (5.3)
-- statement:
--   Let $m_1,m_2,n\ge1$. Observe $n$ pairs $(X_i,Y_i)$ in the matrix completion model: $X_i=e_{j_i}(m_1)e_{k_i}(m_2)^\top$ is the matrix with a single entry $1$ at position $(j_i,k_i)$, and $Y_i\in\mathbb R$. For the target $A_0\in\mathbb R^{m_1\times m_2}$ set
--   $$\mathbf X=\frac{m_1m_2}{n}\sum_{i=1}^nY_iX_i,\qquad \mathbf M=\frac1n\sum_{i=1}^nY_iX_i-\frac{A_0}{m_1m_2},$$
--   so that $\mathbf X-A_0=m_1m_2\mathbf M$. Let $\lambda>0$ satisfy $\lambda\ge2\|\mathbf M\|_\infty$ (the operator norm), let $0<\delta<1$ and $\lambda'=\lambda/(1-\delta)$, and let $\hat A^{\lambda'}$ be the estimator (3.1) with parameter $\lambda'$, a minimizer over all $A\in\mathbb R^{m_1\times m_2}$ of
--   $$\|A-\mathbf X\|_2^2+\lambda'm_1m_2\|A\|_1 .$$
--   Set $\hat r=\operatorname{rank}(\hat A^{\lambda'})$. Then
--
--   $$\hat r\le\operatorname{rank}(A_0).\tag{5.1}$$
--
--   If, in addition, $\min_{j:\,\sigma_j(A_0)\ne0}\sigma_j(A_0)\ge\lambda'm_1m_2$, then
--
--   $$\hat r\ge\operatorname{rank}(A_0)\tag{5.2}$$
--
--   and
--
--   $$\|\hat A^{\lambda'}-A_0\|_2^2\ge\frac{\delta^2}{4(1-\delta)^2}\operatorname{rank}(A_0)\,(\lambda m_1m_2)^2.\tag{5.3}$$
--
--   The estimator thus recovers the rank of a matrix whose nonzero singular values are well separated from zero, and on such matrices its Frobenius error is bounded below at the same rate $\operatorname{rank}(A_0)(\lambda m_1m_2)^2$ as the paper's upper bounds (Corollary 2), so those upper bounds are attained up to constants.
--
--   **Formalization Note** The theorem is stated realization-wise, for every data set on which $\lambda\ge2\|\mathbf M\|_\infty$; the paper's "with $X_i$ i.i.d. uniformly distributed on $\mathcal X$" is used only to identify $\mathbf M=\frac1n\sum_i(Y_iX_i-\mathbb E(Y_iX_i))$ of (2.2) with the matrix above, since $\mathbb E(Y_iX_i)=\mathbb E(\langle A_0,X_i\rangle X_i)=A_0/(m_1m_2)$ under the model (1.1) and the uniform design. The estimator is any minimizer of (3.1) (it is unique). The minimum over $\{j:\sigma_j(A_0)\ne0\}$ is written as a universal statement over the indices with $\sigma_j(A_0)\ne0$, so $A_0=0$ makes the condition vacuous; singular values are 0-based in Lean. The norms are `spectralNorm` ($\|\cdot\|_\infty$), `frobeniusNormSq` ($\|\cdot\|_2^2$) and `nuclearNorm` ($\|\cdot\|_1$).
-- source:
--   Koltchinskii, Lounici, Tsybakov, Nuclear-Norm Penalization and Optimal Rates for Noisy Low-Rank Matrix Completion, arXiv:1011.6256v4, p. 20, Theorem 8, (5.1)–(5.3)

import Mathlib
import Definitions.Def_KLTNuclear_RankRecovery_Model

open MatrixCompletion

namespace KLTNuclear.RankRecovery

/-- Theorem 8 (p. 20), (5.1)–(5.3): with `λ ≥ 2‖𝐌‖∞`, `0 < δ < 1` and `λ′ = λ/(1 − δ)`, the
estimator `Â^{λ′}` of (3.1) has rank at most `rank(A₀)`; if moreover every nonzero singular
value of `A₀` is at least `λ′m₁m₂`, its rank equals `rank(A₀)` and
`‖Â^{λ′} − A₀‖₂² ≥ δ²/(4(1 − δ)²) · rank(A₀) · (λm₁m₂)²`. -/
theorem theorem_8 {m₁ m₂ n : ℕ} (hn : 0 < n) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (idx : Fin n → Fin m₁ × Fin m₂) (y : Fin n → ℝ) (A₀ : RealMatrix m₁ m₂)
    (lam δ : ℝ) (hlam : 0 < lam) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hM : 2 * spectralNorm (noiseMatrix idx y A₀) ≤ lam)
    (Ahat : RealMatrix m₁ m₂) (hAhat : IsEstimator idx y (lam / (1 - δ)) Ahat) :
    Ahat.rank ≤ A₀.rank ∧
      ((∀ j : ℕ, singularValue A₀ j ≠ 0 →
          lam / (1 - δ) * ((m₁ : ℝ) * m₂) ≤ singularValue A₀ j) →
        A₀.rank ≤ Ahat.rank ∧
          δ ^ 2 / (4 * (1 - δ) ^ 2) * (A₀.rank : ℝ) * (lam * ((m₁ : ℝ) * m₂)) ^ 2 ≤
            frobeniusNormSq (Ahat - A₀)) := by sorry

end KLTNuclear.RankRecovery

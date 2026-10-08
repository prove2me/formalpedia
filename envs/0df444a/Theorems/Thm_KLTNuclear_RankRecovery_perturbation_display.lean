-- Prove2me | Theorems.Thm_KLTNuclear_RankRecovery_perturbation_display
-- name    : KLTNuclear.RankRecovery.perturbation_display
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:48:47.973266+00:00
-- url     : https://prove2.me/theorems/0833bc5d-b6f4-4a57-8cb0-5f5b8b6e95b2
-- title:
--   Proof of Theorem 8, p. 20 — $|\sigma_j(\mathbf X)-\sigma_j(A_0)|\le\sigma_1(\mathbf X-A_0)=m_1m_2\|\mathbf M\|_\infty\le\lambda m_1m_2/2$
-- statement:
--   Consider the matrix completion data of the module `KLTNuclear.RankRecovery.Model`: positions $(j_i,k_i)$, responses $Y_i$ ($i=1,\dots,n$, $n\ge1$), a matrix $A_0\in\mathbb R^{m_1\times m_2}$ ($m_1,m_2\ge1$), the matrix $\mathbf X=\frac{m_1m_2}{n}\sum_iY_iX_i$ and $\mathbf M=\frac1n\sum_iY_iX_i-A_0/(m_1m_2)$. Let $\lambda>0$, $0<\delta<1$, $\lambda'=\lambda/(1-\delta)$, and assume $\lambda\ge2\|\mathbf M\|_\infty$. Then, for all $j=1,\dots,m_1\wedge m_2$,
--
--   $$|\sigma_j(\mathbf X)-\sigma_j(A_0)|\le\sigma_1(\mathbf X-A_0)=m_1m_2\|\mathbf M\|_\infty\le\frac{\lambda m_1m_2}{2}=(1-\delta)\frac{\lambda'm_1m_2}{2}.$$
--
--   The first inequality is the perturbation bound for singular values (Weyl's inequality, which the paper cites from Stewart and Sun, p. 203): each singular value moves by at most the operator norm of the perturbation. It is what transfers the singular values of $A_0$ to those of $\mathbf X$ in both rank statements of Theorem 8.
--
--   **Formalization Note** $\sigma_1(\cdot)=\|\cdot\|_\infty$ is `spectralNorm`; the paper's $\sigma_j$ is `singularValue · (j-1)`, so $j=1,\dots,m_1\wedge m_2$ becomes `j < min m₁ m₂`. The identification of $\mathbf M$ with (2.2) is explained in the Model module.
-- source:
--   Koltchinskii, Lounici, Tsybakov, Nuclear-Norm Penalization and Optimal Rates for Noisy Low-Rank Matrix Completion, arXiv:1011.6256v4, p. 20, proof of Theorem 8, first display (cf. [25], page 203)

import Mathlib
import Definitions.Def_KLTNuclear_RankRecovery_Model

open MatrixCompletion

namespace KLTNuclear.RankRecovery

/-- Proof of Theorem 8 (p. 20), first display: for `j = 1, …, m₁ ∧ m₂` (Lean index `j - 1`),
`|σ_j(𝐗) − σ_j(A₀)| ≤ σ₁(𝐗 − A₀) = m₁m₂‖𝐌‖∞ ≤ λm₁m₂/2 = (1 − δ)λ′m₁m₂/2`. -/
theorem perturbation_display {m₁ m₂ n : ℕ} (hn : 0 < n) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (idx : Fin n → Fin m₁ × Fin m₂) (y : Fin n → ℝ) (A₀ : RealMatrix m₁ m₂)
    (lam δ : ℝ) (hlam : 0 < lam) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hM : 2 * spectralNorm (noiseMatrix idx y A₀) ≤ lam) :
    (∀ j : ℕ, j < min m₁ m₂ →
        |singularValue (bigX idx y) j - singularValue A₀ j| ≤ spectralNorm (bigX idx y - A₀)) ∧
      spectralNorm (bigX idx y - A₀) = (m₁ : ℝ) * m₂ * spectralNorm (noiseMatrix idx y A₀) ∧
      (m₁ : ℝ) * m₂ * spectralNorm (noiseMatrix idx y A₀) ≤ lam * ((m₁ : ℝ) * m₂) / 2 ∧
      lam * ((m₁ : ℝ) * m₂) / 2 = (1 - δ) * (lam / (1 - δ) * ((m₁ : ℝ) * m₂) / 2) := by sorry

end KLTNuclear.RankRecovery

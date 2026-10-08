-- Prove2me | Theorems.Thm_KLTNuclear_RankRecovery_rank_estimator
-- name    : KLTNuclear.RankRecovery.rank_estimator
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:48:24.733003+00:00
-- url     : https://prove2.me/theorems/b3a9f33e-29e0-49c4-aa2d-b6042729e3a8
-- title:
--   Proof of Theorem 8, p. 20 — rank$(\hat A^\lambda)=\#\{j:\sigma_j(\mathbf X)>\lambda m_1m_2/2\}$, from (3.2)
-- statement:
--   Consider the matrix completion data of the module `KLTNuclear.RankRecovery.Model` ($n,m_1,m_2\ge1$), the matrix $\mathbf X=\frac{m_1m_2}{n}\sum_iY_iX_i$, and $\lambda>0$. Let $\hat A^\lambda$ be a minimizer over $\mathbb R^{m_1\times m_2}$ of the objective (3.1),
--   $$F(A)=\|A-\mathbf X\|_2^2+\lambda m_1m_2\|A\|_1 .$$
--   Then the rank of $\hat A^\lambda$ is the number of singular values of $\mathbf X$ strictly above the threshold $\lambda m_1m_2/2$:
--
--   $$\operatorname{rank}(\hat A^\lambda)=\#\Big\{j\in\{1,\dots,m_1\wedge m_2\}:\ \sigma_j(\mathbf X)>\frac{\lambda m_1m_2}{2}\Big\}.$$
--
--   Equivalently, if $\hat r=\operatorname{rank}(\hat A^\lambda)\ge1$ then $\sigma_{\hat r}(\mathbf X)>\lambda m_1m_2/2$, and $\sigma_j(\mathbf X)>\lambda m_1m_2/2$ for $j\le r$ forces $\hat r\ge r$. This is the consequence of the soft-thresholding representation (3.2), $\hat A^\lambda=\sum_j(\sigma_j(\mathbf X)-\lambda m_1m_2/2)_+u_j(\mathbf X)v_j(\mathbf X)^\top$, that the proof of Theorem 8 uses for both (5.1) and (5.2).
--
--   **Formalization Note** The statement is about the minimizer of (3.1), not about the formula (3.2); (3.2) itself is the open platform item `CaiCandesShen.Convergence.shrink_eq_prox` (Cai–Candès–Shen, Theorem 2.1) after halving the objective, with $\tau=\lambda m_1m_2/2$, and is not posed again. Singular values are 0-based in Lean (`singularValue · j` is $\sigma_{j+1}$), so the count runs over `j ∈ range (min m₁ m₂)`.
-- source:
--   Koltchinskii, Lounici, Tsybakov, Nuclear-Norm Penalization and Optimal Rates for Noisy Low-Rank Matrix Completion, arXiv:1011.6256v4, p. 20, proof of Theorem 8 ('Since, by (3.2), σ_r̂(X) > λ′m1m2/2'); p. 12 (3.1)–(3.2)

import Mathlib
import Definitions.Def_KLTNuclear_RankRecovery_Model

open MatrixCompletion

namespace KLTNuclear.RankRecovery

/-- Proof of Theorem 8 (p. 20), "by (3.2)": the rank of the estimator `Â^λ` of (3.1) is the
number of singular values of `𝐗` strictly above `λm₁m₂/2`. -/
theorem rank_estimator {m₁ m₂ n : ℕ} (hn : 0 < n) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (idx : Fin n → Fin m₁ × Fin m₂) (y : Fin n → ℝ)
    (lam : ℝ) (hlam : 0 < lam)
    (Ahat : RealMatrix m₁ m₂) (hAhat : IsEstimator idx y lam Ahat) :
    Ahat.rank = ((Finset.range (min m₁ m₂)).filter
      (fun j => lam * ((m₁ : ℝ) * m₂) / 2 < singularValue (bigX idx y) j)).card := by sorry

end KLTNuclear.RankRecovery

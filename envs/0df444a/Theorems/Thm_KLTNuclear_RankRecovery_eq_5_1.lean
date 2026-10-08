-- Prove2me | Theorems.Thm_KLTNuclear_RankRecovery_eq_5_1
-- name    : KLTNuclear.RankRecovery.eq_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:48:25.084831+00:00
-- url     : https://prove2.me/theorems/cfdbed56-03eb-42e2-b16c-a5631734db43
-- title:
--   (5.1), p. 20 — rank$(\hat A^{\lambda'})\le$ rank$(A_0)$ when $\lambda\ge2\|\mathbf M\|_\infty$
-- statement:
--   Consider the matrix completion data of the module `KLTNuclear.RankRecovery.Model` ($n,m_1,m_2\ge1$), a matrix $A_0$, the matrices $\mathbf X$ and $\mathbf M=\frac1n\sum_iY_iX_i-A_0/(m_1m_2)$. Let $\lambda>0$ satisfy $\lambda\ge2\|\mathbf M\|_\infty$, let $0<\delta<1$ and $\lambda'=\lambda/(1-\delta)$, and let $\hat A^{\lambda'}$ be a minimizer of (3.1) with parameter $\lambda'$. Then $\hat r=\operatorname{rank}(\hat A^{\lambda'})$ satisfies
--
--   $$\hat r\le\operatorname{rank}(A_0).$$
--
--   The nuclear-norm penalized estimator, with its parameter inflated by the factor $1/(1-\delta)$, never overestimates the rank of the target matrix.
--
--   **Formalization Note** The statement is realization-wise: it holds for every data set on which $\lambda\ge2\|\mathbf M\|_\infty$. The paper's hypothesis "$X_i$ i.i.d. uniformly distributed on $\mathcal X$" enters only through the form of $\mathbf M$ (see the Model module).
-- source:
--   Koltchinskii, Lounici, Tsybakov, Nuclear-Norm Penalization and Optimal Rates for Noisy Low-Rank Matrix Completion, arXiv:1011.6256v4, p. 20, Theorem 8, (5.1)

import Mathlib
import Definitions.Def_KLTNuclear_RankRecovery_Model

open MatrixCompletion

namespace KLTNuclear.RankRecovery

/-- (5.1) of Theorem 8 (p. 20): `r̂ = rank(Â^{λ′}) ≤ rank(A₀)` when `λ ≥ 2‖𝐌‖∞`,
`λ′ = λ/(1 − δ)`, `0 < δ < 1`. -/
theorem eq_5_1 {m₁ m₂ n : ℕ} (hn : 0 < n) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (idx : Fin n → Fin m₁ × Fin m₂) (y : Fin n → ℝ) (A₀ : RealMatrix m₁ m₂)
    (lam δ : ℝ) (hlam : 0 < lam) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hM : 2 * spectralNorm (noiseMatrix idx y A₀) ≤ lam)
    (Ahat : RealMatrix m₁ m₂) (hAhat : IsEstimator idx y (lam / (1 - δ)) Ahat) :
    Ahat.rank ≤ A₀.rank := by sorry

end KLTNuclear.RankRecovery

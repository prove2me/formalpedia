-- Prove2me | Theorems.Thm_KLTNuclear_RankRecovery_eq_5_2
-- name    : KLTNuclear.RankRecovery.eq_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:48:21.113017+00:00
-- url     : https://prove2.me/theorems/d1fa350b-f4a6-4628-b617-f47c90804791
-- title:
--   (5.2), p. 20 — rank$(\hat A^{\lambda'})\ge$ rank$(A_0)$ above the gap $\lambda'm_1m_2$
-- statement:
--   In the setting of (5.1) (data with $n,m_1,m_2\ge1$, $\lambda>0$ with $\lambda\ge2\|\mathbf M\|_\infty$, $0<\delta<1$, $\lambda'=\lambda/(1-\delta)$, $\hat A^{\lambda'}$ a minimizer of (3.1) with parameter $\lambda'$), assume in addition that every nonzero singular value of $A_0$ is at least $\lambda'm_1m_2$:
--   $$\min_{j:\,\sigma_j(A_0)\ne0}\sigma_j(A_0)\ge\lambda'm_1m_2 .$$
--   Then
--
--   $$\hat r=\operatorname{rank}(\hat A^{\lambda'})\ge\operatorname{rank}(A_0).$$
--
--   Together with (5.1) this gives exact rank recovery: above the singular-value gap $\lambda'm_1m_2$ the estimator has the rank of $A_0$.
--
--   **Formalization Note** The minimum over $\{j:\sigma_j(A_0)\ne0\}$ is written as "for every $j$ with $\sigma_j(A_0)\ne0$, $\lambda'm_1m_2\le\sigma_j(A_0)$", so that the case $A_0=0$ (empty index set) is the vacuous condition, as on the page; no real infimum over a possibly empty set is used.
-- source:
--   Koltchinskii, Lounici, Tsybakov, Nuclear-Norm Penalization and Optimal Rates for Noisy Low-Rank Matrix Completion, arXiv:1011.6256v4, p. 20, Theorem 8, (5.2)

import Mathlib
import Definitions.Def_KLTNuclear_RankRecovery_Model

open MatrixCompletion

namespace KLTNuclear.RankRecovery

/-- (5.2) of Theorem 8 (p. 20): if in addition every nonzero singular value of `A₀` is at
least `λ′m₁m₂`, then `r̂ ≥ rank(A₀)`. -/
theorem eq_5_2 {m₁ m₂ n : ℕ} (hn : 0 < n) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (idx : Fin n → Fin m₁ × Fin m₂) (y : Fin n → ℝ) (A₀ : RealMatrix m₁ m₂)
    (lam δ : ℝ) (hlam : 0 < lam) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hM : 2 * spectralNorm (noiseMatrix idx y A₀) ≤ lam)
    (Ahat : RealMatrix m₁ m₂) (hAhat : IsEstimator idx y (lam / (1 - δ)) Ahat)
    (hgap : ∀ j : ℕ, singularValue A₀ j ≠ 0 →
      lam / (1 - δ) * ((m₁ : ℝ) * m₂) ≤ singularValue A₀ j) :
    A₀.rank ≤ Ahat.rank := by sorry

end KLTNuclear.RankRecovery

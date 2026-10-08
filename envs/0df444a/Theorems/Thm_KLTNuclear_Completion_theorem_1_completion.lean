-- Prove2me | Theorems.Thm_KLTNuclear_Completion_theorem_1_completion
-- name    : KLTNuclear.Completion.theorem_1_completion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:41:48.122593+00:00
-- url     : https://prove2.me/theorems/465f0348-a204-48d7-96d0-4caeed415d45
-- title:
--   Theorem 1 for USR matrix completion — if $\lambda\ge2\|\mathbf M\|_\infty$, (3.5) holds for all $A$
-- statement:
--   Let $n, m_1, m_2\ge1$. Let $(X_i,Y_i)$, $i=1,\dots,n$, be random pairs on a probability space, where each $X_i$ is uniformly distributed on the matrix completion basis $\mathcal X$ and each $Y_i$ is an integrable real random variable, and assume the trace regression model $\mathbb E(Y_i\mid X_i)=\operatorname{tr}(X_i^\top A_0)$ for some $A_0\in\mathbb R^{m_1\times m_2}$. Let $\lambda>0$ and let $\mathbf M=\frac1n\sum_i(Y_iX_i-\mathbb E(Y_iX_i))$. Fix a sample point $\omega$ at which
--   $$\lambda\ge2\|\mathbf M\|_\infty ,$$
--   and let $\hat A^\lambda$ be any minimizer over $\mathbb R^{m_1\times m_2}$ of the objective (3.1) at $\omega$. Then for every $A\in\mathbb R^{m_1\times m_2}$,
--   $$\|\hat A^\lambda-A_0\|_2^2\le\|A-A_0\|_2^2+m_1m_2\min\Big\{2\lambda\|A\|_1,\ \Big(\frac{1+\sqrt2}{2}\Big)^2m_1m_2\lambda^2\operatorname{rank}(A)\Big\}.$$
--
--   This is Theorem 1 (2.3)–(2.4) of the paper specialized to matrix completion with $\mathbb A=\mathbb R^{m_1\times m_2}$ and $\mu=\sqrt{m_1m_2}$, multiplied through by $m_1m_2$: a deterministic statement that turns any high-probability bound on $\|\mathbf M\|_\infty$ into an oracle inequality.
--
--   **Formalization Note** The statement is realization-wise: $\omega$ is fixed and $\lambda\ge2\|\mathbf M(\omega)\|_\infty$ is a hypothesis. Integrability of $Y_i$ is the standing requirement under which $\mathbb E(Y_i\mid X_i)$ and $\mathbb E(Y_iX_i)$ are defined; independence of the pairs is not used by Theorem 1 and is not assumed. $\lambda>0$ is the standing assumption of (1.6), p. 4.
-- source:
--   Koltchinskii, Lounici, Tsybakov, Nuclear-Norm Penalization and Optimal Rates for Noisy Low-Rank Matrix Completion, arXiv:1011.6256v4, p. 6, Theorem 1 (2.3)–(2.4), applied as on p. 12 (§3, (3.1)) and p. 14 ((3.5), 'Theorems 3 and 4 follow immediately from Theorem 1')

import Mathlib
import Definitions.Def_KLTNuclear_Completion_Model

open MatrixCompletion MeasureTheory ProbabilityTheory

namespace KLTNuclear.Completion

/-- Theorem 1, p. 6, for USR matrix completion (§3, pp. 12 and 14): in the trace regression model
(1.1) with design matrices `X_i` uniformly distributed on `𝒳` and integrable responses, at every
sample point `ω` at which `λ ≥ 2‖M‖∞`, every minimizer `Â` of the objective (3.1) satisfies the
oracle inequality (3.5) for all `A ∈ ℝ^{m₁×m₂}` simultaneously. -/
theorem theorem_1_completion {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {n m₁ m₂ : ℕ} (hn : 0 < n) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (I : Fin n → Ω → Fin m₁ × Fin m₂) (hI : ∀ i, UniformIndex P (I i))
    (Y : Fin n → Ω → ℝ) (hY : ∀ i, Integrable (Y i) P)
    (A₀ : RealMatrix m₁ m₂) (hmodel : TraceRegressionModel P (designMatrix I) Y A₀)
    (lam : ℝ) (hlam : 0 < lam) (ω : Ω)
    (hM : 2 * spectralNorm (KLTNuclear.Oracle.noiseMatrix P (designMatrix I) Y ω) ≤ lam)
    (Â : RealMatrix m₁ m₂) (hÂ : IsCompletionEstimator (designMatrix I) Y lam ω Â)
    (A : RealMatrix m₁ m₂) :
    frobeniusNormSq (Â - A₀) ≤ frobeniusNormSq (A - A₀) + (m₁ : ℝ) * m₂ *
      min (2 * lam * nuclearNorm A)
        (((1 + Real.sqrt 2) / 2) ^ 2 * ((m₁ : ℝ) * m₂) * lam ^ 2 * (A.rank : ℝ)) := by sorry

end KLTNuclear.Completion

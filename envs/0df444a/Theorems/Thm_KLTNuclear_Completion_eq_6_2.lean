-- Prove2me | Theorems.Thm_KLTNuclear_Completion_eq_6_2
-- name    : KLTNuclear.Completion.eq_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:42:02.482586+00:00
-- url     : https://prove2.me/theorems/f1839b3a-deb7-4d2f-a6d8-79a434e4f7cf
-- title:
--   (6.2) — $\|X\|=1$, $\|\mathbb E X\|=\sqrt{1/(m_1m_2)}$, $\sigma_X^2=1/(m_1\wedge m_2)$ for $X$ uniform on $\mathcal X$
-- statement:
--   Let $m_1, m_2\ge1$ and let $X$ be a random matrix uniformly distributed on the matrix completion basis $\mathcal X=\{e_j(m_1)e_k^\top(m_2)\}$. Write $\|\cdot\|$ for the operator norm and
--   $$\sigma_X=\max\big\{\|\mathbb E(XX^\top)\|^{1/2},\ \|\mathbb E(X^\top X)\|^{1/2}\big\}$$
--   (the quantity $\sigma_Z$ of Proposition 1 for the single matrix $X$). Then
--   $$\|X\|=1,\qquad\|\mathbb E(X)\|=\sqrt{\frac1{m_1m_2}},\qquad\sigma_X^2=\frac1{m_1\wedge m_2}.$$
--
--   These are the three facts the proof of Lemma 1 feeds into Proposition 1: they give $\|Z_i\|\le2\eta$ and $\sigma_Z\le\eta\sigma_X$ for $Z_i=Y_iX_i-\mathbb E(Y_iX_i)$.
--
--   **Formalization Note** $\|X\|=1$ is stated for every sample point. $\sigma_X$ is the uncentred quantity (no subtraction of $\mathbb E X$), exactly as $\sigma_Z$ of Proposition 1 with $n=1$; $m_1\wedge m_2=\min(m_1,m_2)$.
-- source:
--   Koltchinskii, Lounici, Tsybakov, Nuclear-Norm Penalization and Optimal Rates for Noisy Low-Rank Matrix Completion, arXiv:1011.6256v4, p. 28, proof of Lemma 1, (6.2)

import Mathlib
import Definitions.Def_KLTNuclear_Completion_Model

open MatrixCompletion MeasureTheory ProbabilityTheory

namespace KLTNuclear.Completion

/-- (6.2), proof of Lemma 1, p. 28: for a random matrix `X` uniformly distributed on the matrix
completion basis `𝒳`, `‖X‖ = 1`, `‖𝔼(X)‖ = √(1/(m₁m₂))` and `σ_X² = 1/(m₁ ∧ m₂)`, where
`σ_X` is the quantity `σ_Z` of Proposition 1 for the single matrix `X` (`n = 1`) and
`‖·‖` is the operator norm. -/
theorem eq_6_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {m₁ m₂ : ℕ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (J : Ω → Fin m₁ × Fin m₂) (hJ : UniformIndex P J) :
    (∀ ω, spectralNorm (coordinateMatrix (J ω).1 (J ω).2) = 1) ∧
    spectralNorm (matrixMean P fun ω => coordinateMatrix (J ω).1 (J ω).2)
        = Real.sqrt (1 / ((m₁ : ℝ) * m₂)) ∧
    sigmaZ P (fun (_ : Fin 1) ω => coordinateMatrix (J ω).1 (J ω).2) ^ 2
        = 1 / ((min m₁ m₂ : ℕ) : ℝ) := by sorry

end KLTNuclear.Completion

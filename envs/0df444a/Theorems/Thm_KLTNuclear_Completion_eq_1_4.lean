-- Prove2me | Theorems.Thm_KLTNuclear_Completion_eq_1_4
-- name    : KLTNuclear.Completion.eq_1_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:41:26.551234+00:00
-- url     : https://prove2.me/theorems/687016d9-3762-448d-8b92-16420106118f
-- title:
--   (1.4) — isometry $\|A\|^2_{L_2(\Pi)}=\mu^{-2}\|A\|_2^2$, $\mu=\sqrt{m_1m_2}$, for the uniform design
-- statement:
--   Let $n, m_1, m_2\ge1$ and let $X_1,\dots,X_n$ be random matrices, each uniformly distributed on the matrix completion basis $\mathcal X=\{e_j(m_1)e_k^\top(m_2)\}$. Set $\mu=\sqrt{m_1m_2}$. Then for every matrix $A\in\mathbb R^{m_1\times m_2}$,
--   $$\|A\|_{L_2(\Pi)}^2=\frac1n\sum_{i=1}^n\mathbb E\big(\langle A,X_i\rangle^2\big)=\mu^{-2}\|A\|_2^2 ,$$
--   where $\|A\|_2$ is the Frobenius norm.
--
--   This isometry is what makes Assumption 1 hold with equality and $\mu=\sqrt{m_1m_2}$ in matrix completion, so that the general oracle inequalities, stated in $L_2(\Pi)$, become Frobenius-norm bounds.
--
--   **Formalization Note** Only the uniform marginal law of each $X_i$ is assumed (the page's "i.i.d." is not needed for this identity, so the statement is slightly more general). $\mu^{-2}$ is written $(\sqrt{m_1m_2})^{-2}$.
-- source:
--   Koltchinskii, Lounici, Tsybakov, Nuclear-Norm Penalization and Optimal Rates for Noisy Low-Rank Matrix Completion, arXiv:1011.6256v4, p. 2, Example 1, (1.4)

import Mathlib
import Definitions.Def_KLTNuclear_Completion_Model

open MatrixCompletion MeasureTheory ProbabilityTheory

namespace KLTNuclear.Completion

/-- (1.4), p. 2 (Example 1): for design matrices `X_i` uniformly distributed on the matrix
completion basis `𝒳` of (1.3), `‖A‖²_{L₂(Π)} = μ⁻² ‖A‖₂²` for every `A ∈ ℝ^{m₁×m₂}`, where
`μ = √(m₁m₂)`. Only the uniform marginal law of each `X_i` is assumed. -/
theorem eq_1_4 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n m₁ m₂ : ℕ} (hn : 0 < n) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (I : Fin n → Ω → Fin m₁ × Fin m₂) (hI : ∀ i, UniformIndex P (I i))
    (A : RealMatrix m₁ m₂) :
    l2NormSq P (designMatrix I) A = (Real.sqrt ((m₁ : ℝ) * m₂) ^ 2)⁻¹ * frobeniusNormSq A := by sorry

end KLTNuclear.Completion

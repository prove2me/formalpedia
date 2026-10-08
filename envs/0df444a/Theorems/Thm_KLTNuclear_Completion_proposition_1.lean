-- Prove2me | Theorems.Thm_KLTNuclear_Completion_proposition_1
-- name    : KLTNuclear.Completion.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:41:44.708191+00:00
-- url     : https://prove2.me/theorems/9a643651-827b-4034-9a48-481dd57642f6
-- title:
--   Proposition 1 — matrix Bernstein inequality for $\|(Z_1+\dots+Z_n)/n\|$
-- statement:
--   Let $n, m_1, m_2\ge1$ and let $Z_1,\dots,Z_n$ be independent random $m_1\times m_2$ matrices with $\mathbb E(Z_i)=0$ and $\|Z_i\|\le U$ almost surely for some constant $U$ and all $i$, where $\|\cdot\|$ is the operator norm. Define
--   $$\sigma_Z=\max\Big\{\Big\|\frac1n\sum_{i=1}^n\mathbb E(Z_iZ_i^\top)\Big\|^{1/2},\ \Big\|\frac1n\sum_{i=1}^n\mathbb E(Z_i^\top Z_i)\Big\|^{1/2}\Big\}$$
--   and $m=m_1+m_2$. Then for all $t>0$, with probability at least $1-e^{-t}$,
--   $$\Big\|\frac{Z_1+\dots+Z_n}{n}\Big\|\le2\max\Big\{\sigma_Z\sqrt{\frac{t+\log m}{n}},\ U\,\frac{t+\log m}{n}\Big\}.$$
--
--   This is the noncommutative Bernstein inequality in the form used to control the stochastic error $\|\mathbf M\|$; the paper derives it from Tropp's rectangular matrix Bernstein inequality (Corollary 9.1 in Tropp, *User-friendly tail bounds for sums of random matrices*, 2012).
--
--   **Formalization Note** "With probability at least $1-e^{-t}$" is encoded as: the (outer) measure of the set where the inequality fails is at most $e^{-t}$. Expectations are entrywise; the random matrices are assumed measurable (as random elements). $\log$ is the natural logarithm. $n, m_1, m_2\ge1$ make the statement non-degenerate.
-- source:
--   Koltchinskii, Lounici, Tsybakov, Nuclear-Norm Penalization and Optimal Rates for Noisy Low-Rank Matrix Completion, arXiv:1011.6256v4, p. 27, Proposition 1

import Mathlib
import Definitions.Def_KLTNuclear_Completion_Model

open MatrixCompletion MeasureTheory ProbabilityTheory

namespace KLTNuclear.Completion

/-- Proposition 1, p. 27 (matrix Bernstein inequality): for independent random `m₁ × m₂`
matrices `Z_1, …, Z_n` with `𝔼 Z_i = 0` and `‖Z_i‖ ≤ U` almost surely, for all `t > 0`, with
probability at least `1 − e^{−t}`,
`‖(Z_1 + ⋯ + Z_n)/n‖ ≤ 2 max { σ_Z √((t + log m)/n), U (t + log m)/n }`, where `m = m₁ + m₂`
and `‖·‖` is the operator norm. The statement bounds the outer measure of the bad event. -/
theorem proposition_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n m₁ m₂ : ℕ} (hn : 0 < n) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (Z : Fin n → Ω → RealMatrix m₁ m₂) (hZmeas : ∀ i, MeasurableMatrix (Z i))
    (hindep : IndepMatrices P Z) (hmean : ∀ i, matrixMean P (Z i) = 0)
    (U : ℝ) (hU : ∀ i, ∀ᵐ ω ∂P, spectralNorm (Z i ω) ≤ U) (t : ℝ) (ht : 0 < t) :
    P {ω | ¬ spectralNorm ((1 / (n : ℝ)) • ∑ i, Z i ω) ≤
        2 * max (sigmaZ P Z * Real.sqrt ((t + Real.log ((m₁ + m₂ : ℕ) : ℝ)) / n))
          (U * ((t + Real.log ((m₁ + m₂ : ℕ) : ℝ)) / n))}
      ≤ ENNReal.ofReal (Real.exp (-t)) := by sorry

end KLTNuclear.Completion

-- Prove2me | Theorems.Thm_KLTNuclear_Completion_lemma_1
-- name    : KLTNuclear.Completion.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:41:17.638101+00:00
-- url     : https://prove2.me/theorems/660c8b84-b8c3-4091-a270-298e035a4099
-- title:
--   Lemma 1 — with probability $\ge1-e^{-t}$, $\|\mathbf M\|\le2\eta\max\{\sqrt{(t+\log m)/((m_1\wedge m_2)n)},\,2(t+\log m)/n\}$
-- statement:
--   Let $n, m_1, m_2\ge1$ and $m=m_1+m_2$. Let $(X_i,Y_i)$, $i=1,\dots,n$, be independent random pairs, where $X_1,\dots,X_n$ are uniformly distributed on the matrix completion basis $\mathcal X$ and $Y_i$ are real random variables with $\max_{i}|Y_i|\le\eta$ almost surely for some constant $\eta$. Let $\mathbf M=\frac1n\sum_{i=1}^n(Y_iX_i-\mathbb E(Y_iX_i))$. Then for any $t>0$, with probability at least $1-e^{-t}$,
--   $$\|\mathbf M\|\le2\eta\max\Big\{\sqrt{\frac{t+\log m}{(m_1\wedge m_2)n}},\ \frac{2(t+\log m)}{n}\Big\},\tag{6.1}$$
--   where $\|\cdot\|$ is the operator norm.
--
--   This controls the stochastic error in the statistical learning setting: no model linking $Y_i$ to $X_i$ is needed, and the $Y_i$ need not be identically distributed.
--
--   **Formalization Note** The page assumes "$X_i$ i.i.d. uniformly distributed on $\mathcal X$" and, as a standing assumption (p. 1), independent pairs $(X_i,Y_i)$; the proof applies Proposition 1 to $Z_i=Y_iX_i-\mathbb E(Y_iX_i)$, which needs the pairs independent, so the Lean assumes the pairs independent (which implies the $X_i$ independent) and each $X_i$ uniform. The design is encoded by the uniform index $I_i$ with $X_i=e_{j_i}e_{k_i}^\top$. Measurability of $Y_i$ is assumed (random variables). The model (1.1) is not assumed. "With probability at least" bounds the outer measure of the failure set by $e^{-t}$.
-- source:
--   Koltchinskii, Lounici, Tsybakov, Nuclear-Norm Penalization and Optimal Rates for Noisy Low-Rank Matrix Completion, arXiv:1011.6256v4, p. 28, Lemma 1, (6.1); standing independence of the pairs, p. 1

import Mathlib
import Definitions.Def_KLTNuclear_Completion_Model

open MatrixCompletion MeasureTheory ProbabilityTheory

namespace KLTNuclear.Completion

/-- Lemma 1, p. 28: let `X_i` be i.i.d. uniformly distributed on `𝒳` (the pairs `(X_i, Y_i)`
independent, as in the standing assumptions of p. 1) and `max_i |Y_i| ≤ η` almost surely. Then for
any `t > 0`, with probability at least `1 − e^{−t}`,
`‖M‖ ≤ 2η max { √((t + log m)/((m₁ ∧ m₂) n)), 2(t + log m)/n }` (6.1), `m = m₁ + m₂`. -/
theorem lemma_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n m₁ m₂ : ℕ} (hn : 0 < n) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (I : Fin n → Ω → Fin m₁ × Fin m₂) (hI : ∀ i, UniformIndex P (I i))
    (Y : Fin n → Ω → ℝ) (hYmeas : ∀ i, Measurable (Y i))
    (hindep : iIndepFun (fun i ω => (I i ω, Y i ω)) P)
    (η : ℝ) (hη : ∀ᵐ ω ∂P, ∀ i, |Y i ω| ≤ η) (t : ℝ) (ht : 0 < t) :
    P {ω | ¬ spectralNorm (KLTNuclear.Oracle.noiseMatrix P (designMatrix I) Y ω) ≤
        2 * η * max
          (Real.sqrt ((t + Real.log ((m₁ + m₂ : ℕ) : ℝ)) / (((min m₁ m₂ : ℕ) : ℝ) * n)))
          (2 * (t + Real.log ((m₁ + m₂ : ℕ) : ℝ)) / n)}
      ≤ ENNReal.ofReal (Real.exp (-t)) := by sorry

end KLTNuclear.Completion

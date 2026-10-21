-- Prove2me | Theorems.Thm_LocalDensityLSH_Count_lemma_4
-- name    : LocalDensityLSH.Count.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:22:35.147677+00:00
-- url     : https://prove2.me/theorems/ccd57eee-be33-4ae8-be84-8d383efab839
-- title:
--   Lemma 4, p. 14 — 𝔼[(Σ_{i=1}^S Z_i/S − |𝒜q|)²] ≤ 𝔼[Z²]/S + σ²(W)
-- statement:
--   Under the setting of Lemma 1, let $\widehat N=\frac1S\sum_{i=1}^S Z_i$ be one LSH Count estimate with $S$ samples, and let $Z$ be the weight of any one of the samples. Then
--   $$\mathbb E\left[\left(\frac{\sum_{i=1}^S Z_i}{S}-|\mathcal A_q|\right)^2\right]\ \le\ \frac{\mathbb E[Z^2]}{S}+\sigma^2(W).$$
--
--   The mean squared error of one estimate splits into a sampling term, which decays as $1/S$, and the table bias term $\sigma^2(W)$.
--
--   **Formalization Note.** All samples have the same law, so $\mathbb E[Z^2]$ is stated for each sample index $s$ (the statement is empty when $S=0$, which the paper does not consider). $\mathcal A_q$ is an arbitrary set of indices.
-- source:
--   Wu, Charikar & Natchu, Local Density Estimation in High Dimensions, arXiv:1809.07471v1, Lemma 4 and its proof, p. 14

import Mathlib
import Definitions.Def_LocalDensityLSH_Count_Model
import Definitions.Def_LocalDensityLSH_Count_Estimator

namespace LocalDensityLSH.Count

open MeasureTheory ProbabilityTheory

/-- Lemma 4 (p. 14): `𝔼[(Σ_{i=1}^S Z_i/S − |𝒜q|)²] ≤ 𝔼[Z²]/S + σ²(W)`, where `Z` is the weight of
any one sample. -/
theorem lemma_4 {n t K S : ℕ} (μ : Measure (Table n t)) [IsProbabilityMeasure μ] (I : Finset ℕ)
    (𝒜q : Finset (Fin n)) (hp : ∀ i ∈ 𝒜q, 0 < p μ I i) (hK : 1 ≤ K)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : Fin K → Ω → Table n t) (X : Fin S → Ω → Fin K × Fin n)
    (hrun : IsEstimatorRun μ I P T X) :
    ∀ s : Fin S,
      ∫ ω, (estimate μ I 𝒜q (fun k => T k ω) (fun j => X j ω) - 𝒜q.card) ^ 2 ∂P ≤
        (∫ ω, Zval μ I 𝒜q (fun k => T k ω) (X s ω) ^ 2 ∂P) / (S : ℝ) +
          variance (fun ω => W μ I 𝒜q (fun k => T k ω)) P := by sorry

end LocalDensityLSH.Count

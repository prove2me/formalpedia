-- Prove2me | Theorems.Thm_LocalDensityLSH_Count_lemma_5
-- name    : LocalDensityLSH.Count.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:22:45.173632+00:00
-- url     : https://prove2.me/theorems/78b09814-8427-4608-817a-5d62a0a86f01
-- title:
--   Lemma 5, p. 15 — 𝔼[Z²] = Σ_{x∈𝒜q} Σ_{y∈𝒟} [p(x,y)/(K·p(x)²) + (1 − 1/K) p(y)/p(x)]
-- statement:
--   Under the setting of Lemma 1, the second moment of the weight $Z$ of any sample is
--   $$\mathbb E[Z^2]=\sum_{x\in\mathcal A_q}\sum_{y\in\mathcal D}\left[\frac{p(x,y)}{K\cdot p(x)^2}+\left(1-\frac1K\right)\frac{p(y)}{p(x)}\right],$$
--   where $y$ ranges over all $n$ data points.
--
--   Together with Lemma 4 this gives the sampling term of the error, and it is the input to the sample complexity bound (Lemma 6).
--
--   **Formalization Note.** The identity is stated for every sample index $s$. $\mathcal A_q$ is an arbitrary set of indices.
-- source:
--   Wu, Charikar & Natchu, Local Density Estimation in High Dimensions, arXiv:1809.07471v1, Lemma 5 and its proof, p. 15, (5)

import Mathlib
import Definitions.Def_LocalDensityLSH_Count_Model
import Definitions.Def_LocalDensityLSH_Count_Estimator

namespace LocalDensityLSH.Count

open MeasureTheory ProbabilityTheory

/-- Lemma 5 (p. 15): `𝔼[Z²] = Σ_{x∈𝒜q} Σ_{y∈𝒟} [p(x,y)/(K p(x)²) + (1 − 1/K) p(y)/p(x)]`. -/
theorem lemma_5 {n t K S : ℕ} (μ : Measure (Table n t)) [IsProbabilityMeasure μ] (I : Finset ℕ)
    (𝒜q : Finset (Fin n)) (hp : ∀ i ∈ 𝒜q, 0 < p μ I i) (hK : 1 ≤ K)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : Fin K → Ω → Table n t) (X : Fin S → Ω → Fin K × Fin n)
    (hrun : IsEstimatorRun μ I P T X) :
    ∀ s : Fin S,
      ∫ ω, Zval μ I 𝒜q (fun k => T k ω) (X s ω) ^ 2 ∂P =
        ∑ x ∈ 𝒜q, ∑ y : Fin n,
          (p2 μ I x y / ((K : ℝ) * p μ I x ^ 2) + (1 - 1 / (K : ℝ)) * (p μ I y / p μ I x)) := by sorry

end LocalDensityLSH.Count

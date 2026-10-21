-- Prove2me | Theorems.Thm_LocalDensityLSH_Count_lemma_2
-- name    : LocalDensityLSH.Count.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:22:40.404264+00:00
-- url     : https://prove2.me/theorems/adab60e5-cd54-4fb6-8faa-fc0692d99b2a
-- title:
--   Lemma 2, p. 10 — σ²(W) = (1/K) Σ_{x,y∈𝒜q} (p(x,y)/(p(x)p(y)) − 1)
-- statement:
--   Under the setting of Lemma 1 ($K\ge1$ tables drawn independently from the hash law $\mu$, and $p(x)>0$ on $\mathcal A_q$), the variance of the table bias $W$ is
--   $$\sigma^2(W)=\frac1K\sum_{x,y\in\mathcal A_q}\left(\frac{p(x,y)}{p(x)\,p(y)}-1\right),$$
--   where the sum runs over ordered pairs, including $x=y$ (for which $p(x,x)=p(x)$).
--
--   The formula shows that the table bias decays as $1/K$ and is controlled by the pairwise collision correlations of the points of interest; it is the input to the bound on the number of tables (Lemma 3).
--
--   **Formalization Note.** $\sigma^2$ is `ProbabilityTheory.variance`. $\mathcal A_q$ is an arbitrary set of indices.
-- source:
--   Wu, Charikar & Natchu, Local Density Estimation in High Dimensions, arXiv:1809.07471v1, Lemma 2, p. 10 (p(x, y) defined just above it); proof p. 11

import Mathlib
import Definitions.Def_LocalDensityLSH_Count_Model
import Definitions.Def_LocalDensityLSH_Count_Estimator

namespace LocalDensityLSH.Count

open MeasureTheory ProbabilityTheory

/-- Lemma 2 (p. 10): `σ²(W) = (1/K) Σ_{x,y ∈ 𝒜q} (p(x,y)/(p(x)p(y)) − 1)`. -/
theorem lemma_2 {n t K S : ℕ} (μ : Measure (Table n t)) [IsProbabilityMeasure μ] (I : Finset ℕ)
    (𝒜q : Finset (Fin n)) (hp : ∀ i ∈ 𝒜q, 0 < p μ I i) (hK : 1 ≤ K)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : Fin K → Ω → Table n t) (X : Fin S → Ω → Fin K × Fin n)
    (hrun : IsEstimatorRun μ I P T X) :
    variance (fun ω => W μ I 𝒜q (fun k => T k ω)) P =
      (1 / (K : ℝ)) * ∑ x ∈ 𝒜q, ∑ y ∈ 𝒜q, (p2 μ I x y / (p μ I x * p μ I y) - 1) := by sorry

end LocalDensityLSH.Count

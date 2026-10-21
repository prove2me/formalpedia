-- Prove2me | Theorems.Thm_LocalDensityLSH_Count_lemma_1
-- name    : LocalDensityLSH.Count.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:22:40.156435+00:00
-- url     : https://prove2.me/theorems/3e5f19f8-c17d-4eb1-9948-27a8aa4487d4
-- title:
--   Lemma 1, p. 10 — given the tables the sample weight Z has mean W, and 𝔼(W) = 𝔼(Z) = |𝒜q|
-- statement:
--   Fix a hash law $\mu$, a Hamming range $\mathcal I$ and a set $\mathcal A_q$ of data points with $p(x)>0$ for every $x\in\mathcal A_q$. Run one LSH Count estimator with $K\ge1$ tables and $S$ samples. Then:
--
--   1. for every realization $\tau$ of the $K$ tables, the mean of the weight $Z$ of a sample drawn from the pool is $W(\tau)$:
--   $$\mathbb E(Z\mid \tau)=\sum_{(k,x)}w_\tau(k,x)\,Z(k,x)=W(\tau);$$
--   2. $\mathbb E(W)=|\mathcal A_q|$;
--   3. every sample's weight is unbiased: $\mathbb E(Z_s)=|\mathcal A_q|$ for each $s$.
--
--   This is the unbiasedness of the importance-sampling weight on which the whole analysis of LSH Count rests: the samples are unbiased for $W$, and $W$ is unbiased for the count.
--
--   **Formalization Note.** The paper conditions on "a specific realization of hash functions, or equivalently, given $W$"; these are not equivalent, and its proof conditions on the tables, which is what part 1 states, as an identity for every table configuration. $\mathcal A_q$ is an arbitrary set of indices here (the geometry of $v$, $q$, $\mathcal A$ plays no role), which makes the statement more general. The hypothesis $p(x)>0$ on $\mathcal A_q$ is implicit in the paper's division by $p(x)$.
-- source:
--   Wu, Charikar & Natchu, Local Density Estimation in High Dimensions, arXiv:1809.07471v1, Lemma 1 and its proof, p. 10

import Mathlib
import Definitions.Def_LocalDensityLSH_Count_Model
import Definitions.Def_LocalDensityLSH_Count_Estimator

namespace LocalDensityLSH.Count

open MeasureTheory ProbabilityTheory

/-- Lemma 1 (p. 10). Given the tables, the sampler's mean weight is `W`; `𝔼(W) = |𝒜q|`; and every
sample's weight `Z` has `𝔼(Z) = |𝒜q|`. -/
theorem lemma_1 {n t K S : ℕ} (μ : Measure (Table n t)) [IsProbabilityMeasure μ] (I : Finset ℕ)
    (𝒜q : Finset (Fin n)) (hp : ∀ i ∈ 𝒜q, 0 < p μ I i) (hK : 1 ≤ K)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : Fin K → Ω → Table n t) (X : Fin S → Ω → Fin K × Fin n)
    (hrun : IsEstimatorRun μ I P T X) :
    (∀ τs : Fin K → Table n t,
        ∑ y, (samplerWeight I τs y).toReal * Zval μ I 𝒜q τs y = W μ I 𝒜q τs) ∧
      ∫ ω, W μ I 𝒜q (fun k => T k ω) ∂P = (𝒜q.card : ℝ) ∧
      ∀ s, ∫ ω, Zval μ I 𝒜q (fun k => T k ω) (X s ω) ∂P = (𝒜q.card : ℝ) := by sorry

end LocalDensityLSH.Count

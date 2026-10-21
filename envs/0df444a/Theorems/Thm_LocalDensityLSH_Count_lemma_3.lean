-- Prove2me | Theorems.Thm_LocalDensityLSH_Count_lemma_3
-- name    : LocalDensityLSH.Count.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:22:48.894721+00:00
-- url     : https://prove2.me/theorems/3f7cd09c-8d9f-4db2-9276-2aa2d1273b35
-- title:
--   Lemma 3, p. 11 — K ≥ 8/(ε² min_{x∈𝒜q} p(x)) tables give σ²(W) ≤ ε²|𝒜q|²/8, so W is within ε|𝒜q| of |𝒜q| with probability 7/8
-- statement:
--   Let $\mathcal A_q$ be nonempty with $p(x)>0$ for all $x\in\mathcal A_q$, let $\varepsilon>0$ and $p_{\min}=\min_{x\in\mathcal A_q}p(x)$. If the number of tables satisfies
--   $$K\ \ge\ \frac{8}{\varepsilon^2\,p_{\min}},$$
--   then
--   1. $\sigma^2(W)\le \varepsilon^2|\mathcal A_q|^2/8$, and
--   2. $\mathbb P\big(|W-|\mathcal A_q||<\varepsilon|\mathcal A_q|\big)\ge 7/8$.
--
--   This is the table complexity of LSH Count: with that many tables the bias introduced by the particular realization of the hash functions is small.
--
--   **Formalization Note.** Part 2 is the printed conclusion ("$W$ is within $\varepsilon$ of $|\mathcal A_q|$ (relatively) with probability $7/8$", read as at least $7/8$). Part 1 is the variance bound that the proof establishes and that §5 (p. 16) uses. Nonemptiness of $\mathcal A_q$, $p>0$ on $\mathcal A_q$ and $\varepsilon>0$ are implicit in the paper's $\min$, its division by $p(x)$ and "within $\varepsilon$".
-- source:
--   Wu, Charikar & Natchu, Local Density Estimation in High Dimensions, arXiv:1809.07471v1, Lemma 3, p. 11; proof pp. 11–12, ending at (4)

import Mathlib
import Definitions.Def_LocalDensityLSH_Count_Model
import Definitions.Def_LocalDensityLSH_Count_Estimator

namespace LocalDensityLSH.Count

open MeasureTheory ProbabilityTheory

/-- Lemma 3 (p. 11): if `K ≥ 8/(ε² min_{x∈𝒜q} p(x))`, then `σ²(W) ≤ ε²|𝒜q|²/8` and `W` is within
`ε|𝒜q|` of `|𝒜q|` with probability at least `7/8`. -/
theorem lemma_3 {n t K S : ℕ} (μ : Measure (Table n t)) [IsProbabilityMeasure μ] (I : Finset ℕ)
    (𝒜q : Finset (Fin n)) (hA : 𝒜q.Nonempty) (hp : ∀ i ∈ 𝒜q, 0 < p μ I i)
    (ε : ℝ) (hε : 0 < ε) (hK : 8 / (ε ^ 2 * pmin μ I hA) ≤ (K : ℝ))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : Fin K → Ω → Table n t) (X : Fin S → Ω → Fin K × Fin n)
    (hrun : IsEstimatorRun μ I P T X) :
    variance (fun ω => W μ I 𝒜q (fun k => T k ω)) P ≤ ε ^ 2 * (𝒜q.card : ℝ) ^ 2 / 8 ∧
      7 / 8 ≤ P.real {ω | |W μ I 𝒜q (fun k => T k ω) - 𝒜q.card| < ε * 𝒜q.card} := by sorry

end LocalDensityLSH.Count

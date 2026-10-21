-- Prove2me | Theorems.Thm_LocalDensityLSH_Count_single_estimator_failure
-- name    : LocalDensityLSH.Count.single_estimator_failure
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:22:48.603978+00:00
-- url     : https://prove2.me/theorems/9af3aec7-e55b-44c3-809c-190b6c2f4857
-- title:
--   §5, p. 16, single-estimator failure ≤ 1/4 — under the bounds on K and S, ℙ(|Σ_{i=1}^S Z_i/S − |𝒜q|| ≥ ε|𝒜q|) ≤ 1/4
-- statement:
--   Let $\mathcal A_q$ be nonempty with $p(x)>0$ for all $x\in\mathcal A_q$, let $\varepsilon>0$ and $p_{\min}=\min_{x\in\mathcal A_q}p(x)$, and suppose
--   $$K\ge\frac{8}{\varepsilon^2p_{\min}},\qquad S\ge\frac{8(1+\varepsilon^2)\,\mathbb E(C_q(\mathcal I))}{\varepsilon^2|\mathcal A_q|\,p_{\min}}.$$
--   Then one LSH Count estimator with $K$ tables and $S$ samples fails with probability at most $1/4$:
--   $$\mathbb P\left(\left|\frac{\sum_{i=1}^S Z_i}{S}-|\mathcal A_q|\right|\ge\varepsilon|\mathcal A_q|\right)\le\frac14.$$
--
--   This is the constant-probability guarantee that the median-of-means step boosts to probability $1-\delta$.
--
--   **Formalization Note.** The bounds on $K$ and $S$ are those of Lemmas 3 and 6, with the constant of Lemma 6's proof (see that item).
-- source:
--   Wu, Charikar & Natchu, Local Density Estimation in High Dimensions, arXiv:1809.07471v1, §5, p. 16 (paragraphs between the Chernoff step and Lemma 6)

import Mathlib
import Definitions.Def_LocalDensityLSH_Count_Model
import Definitions.Def_LocalDensityLSH_Count_Estimator

namespace LocalDensityLSH.Count

open MeasureTheory ProbabilityTheory

/-- §5, p. 16: with `K ≥ 8/(ε² p_min)` and `S ≥ 8(1 + ε²) 𝔼(C_q(ℐ)) / (ε² |𝒜q| p_min)`, one
estimator fails, `|Σ Z_i/S − |𝒜q|| ≥ ε|𝒜q|`, with probability at most `1/4`. -/
theorem single_estimator_failure {n t K S : ℕ} (μ : Measure (Table n t)) [IsProbabilityMeasure μ]
    (I : Finset ℕ) (𝒜q : Finset (Fin n)) (hA : 𝒜q.Nonempty) (hp : ∀ i ∈ 𝒜q, 0 < p μ I i)
    (ε : ℝ) (hε : 0 < ε) (hK : 8 / (ε ^ 2 * pmin μ I hA) ≤ (K : ℝ))
    (hS : 8 * (1 + ε ^ 2) * EC μ I / (ε ^ 2 * (𝒜q.card : ℝ) * pmin μ I hA) ≤ (S : ℝ))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : Fin K → Ω → Table n t) (X : Fin S → Ω → Fin K × Fin n)
    (hrun : IsEstimatorRun μ I P T X) :
    P.real {ω | ε * 𝒜q.card ≤
      |estimate μ I 𝒜q (fun k => T k ω) (fun j => X j ω) - 𝒜q.card|} ≤ 1 / 4 := by sorry

end LocalDensityLSH.Count

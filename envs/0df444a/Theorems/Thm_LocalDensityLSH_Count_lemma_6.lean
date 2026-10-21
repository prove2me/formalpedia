-- Prove2me | Theorems.Thm_LocalDensityLSH_Count_lemma_6
-- name    : LocalDensityLSH.Count.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:22:52.77304+00:00
-- url     : https://prove2.me/theorems/c737cbc4-ea14-427a-8e3b-9cfef2349012
-- title:
--   Lemma 6, p. 16 — with K ≥ 8/(ε² p_min), S ≥ 8(1 + ε²)𝔼(C_q(ℐ))/(ε²|𝒜q| p_min) samples give 𝔼[Z²]/S ≤ ε²|𝒜q|²/8 (with the constant of its proof)
-- statement:
--   Let $\mathcal A_q$ be nonempty with $p(x)>0$ for all $x\in\mathcal A_q$, let $\varepsilon>0$ and $p_{\min}=\min_{x\in\mathcal A_q}p(x)$. Suppose
--   $$K\ge\frac{8}{\varepsilon^2p_{\min}}\qquad\text{and}\qquad S\ \ge\ \frac{8(1+\varepsilon^2)\,\mathbb E(C_q(\mathcal I))}{\varepsilon^2\,|\mathcal A_q|\,p_{\min}},$$
--   where $\mathbb E(C_q(\mathcal I))=\sum_{y\in\mathcal D}p(y)$. Then, for the weight $Z$ of any sample,
--   $$\frac{\mathbb E[Z^2]}{S}\ \le\ \frac{\varepsilon^2|\mathcal A_q|^2}{8}.$$
--
--   This is the sample complexity of LSH Count: the ratio $\mathbb E(C_q(\mathcal I))/(|\mathcal A_q|\,p_{\min})$ replaces the ratio $n/|\mathcal A_q|$ of naive random sampling.
--
--   **Formalization Note.** The paper states $S\in O(\cdot)$; here the $O(\cdot)$ is pinned to the constant of its proof. The printed proof (p. 17) concludes with $S\ge\sum_{x\in\mathcal A_q}\sum_{y\in\mathcal D}(1+\varepsilon^2)\frac{p(y)}{p(x)}\big/(\varepsilon^2|\mathcal A_q|^2)$, which omits the factor $8$ that its target $\mathbb E[Z^2]/S\le\varepsilon^2|\mathcal A_q|^2/8$ needs (with $p\equiv1$ and $\mathcal A_q=\mathcal D$ the printed bound fails); the factor $8$ is restored, and $\sum_{x\in\mathcal A_q}1/p(x)\le|\mathcal A_q|/p_{\min}$ is used to reach the form above. The added hypotheses are those of Lemma 3.
-- source:
--   Wu, Charikar & Natchu, Local Density Estimation in High Dimensions, arXiv:1809.07471v1, Lemma 6, p. 16; proof pp. 16–17

import Mathlib
import Definitions.Def_LocalDensityLSH_Count_Model
import Definitions.Def_LocalDensityLSH_Count_Estimator

namespace LocalDensityLSH.Count

open MeasureTheory ProbabilityTheory

/-- Lemma 6 (p. 16), with the constant of its proof: if `K ≥ 8/(ε² p_min)` and
`S ≥ 8(1 + ε²) 𝔼(C_q(ℐ)) / (ε² |𝒜q| p_min)`, then `𝔼[Z²]/S ≤ ε²|𝒜q|²/8`. -/
theorem lemma_6 {n t K S : ℕ} (μ : Measure (Table n t)) [IsProbabilityMeasure μ] (I : Finset ℕ)
    (𝒜q : Finset (Fin n)) (hA : 𝒜q.Nonempty) (hp : ∀ i ∈ 𝒜q, 0 < p μ I i)
    (ε : ℝ) (hε : 0 < ε) (hK : 8 / (ε ^ 2 * pmin μ I hA) ≤ (K : ℝ))
    (hS : 8 * (1 + ε ^ 2) * EC μ I / (ε ^ 2 * (𝒜q.card : ℝ) * pmin μ I hA) ≤ (S : ℝ))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : Fin K → Ω → Table n t) (X : Fin S → Ω → Fin K × Fin n)
    (hrun : IsEstimatorRun μ I P T X) :
    ∀ s : Fin S,
      (∫ ω, Zval μ I 𝒜q (fun k => T k ω) (X s ω) ^ 2 ∂P) / (S : ℝ) ≤
        ε ^ 2 * (𝒜q.card : ℝ) ^ 2 / 8 := by sorry

end LocalDensityLSH.Count

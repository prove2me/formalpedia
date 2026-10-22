-- Prove2me | Theorems.Thm_GradDOvS_Submod_lemma_EC_1
-- name    : GradDOvS.Submod.lemma_EC_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:17:57.906354+00:00
-- url     : https://prove2.me/theorems/07675e8f-bed0-45eb-998d-92cf44bf7b8e
-- title:
--   Lemma EC.1, p. ec2 (PDF 40) — Azuma's inequality for martingale differences with sub-Gaussian tails (Shamir 2011)
-- statement:
--   Let $X_0,\dots,X_{T-1}$, $T \ge 1$, be a martingale difference sequence with respect to a filtration $(\mathcal F_t)$: $X_t$ is $\mathcal F_{t+1}$-measurable and integrable and $\mathbb E[X_t \mid \mathcal F_t] = 0$. Suppose there are constants $b_1 \ge 1$, $b_2 > 0$ with
--   $$\mathbb P\big(|X_t| \ge a \,\big|\, \mathcal F_t\big) \le 2b_1 e^{-b_2 a^2} \qquad \text{for all } a \ge 0,\ t < T. \tag{EC.1}$$
--   Then for every $\delta > 0$, with probability at least $1-\delta$,
--   $$\frac1T\sum_{t=0}^{T-1} X_t \le \sqrt{\frac{28 b_1}{b_2 T}\log\frac1\delta}.$$
--
--   This is the concentration inequality behind Lemma EC.3.
--
--   **Formalization Note** The printed statement conditions on the past of the sequence itself ("$X_1,\dots,X_{t-1}$", an index typo for $X_0,\dots,X_{t-1}$); here any filtration to which the sequence is adapted is allowed, which contains the printed case (take the natural filtration). The conclusion bounds the probability of the complementary event by $\delta$. The conditional probability is the conditional expectation of the indicator, and the bound is required almost surely for each $a$.
-- source:
--   Zhang, Zheng & Lavaei, arXiv:2010.16250v3, p. ec2 (PDF 40), Lemma EC.1 (citing Shamir 2011)

import Mathlib
import Definitions.Def_GradDOvS_Submod_Model

open MeasureTheory ProbabilityTheory

namespace GradDOvS.Submod

/-- Lemma EC.1, p. ec2 (PDF 40) (Shamir 2011): a martingale difference sequence `X_0, …, X_{T-1}`
(adapted to a filtration `ℱ`, `X_t` being `ℱ_{t+1}`-measurable) with conditional sub-Gaussian tails
`P(|X_t| ≥ a | ℱ_t) ≤ 2 b₁ exp(-b₂ a²)` satisfies, for every `δ > 0`,
`(1/T) ∑_{t<T} X_t ≤ √(28 b₁/(b₂ T) · log(1/δ))` with probability at least `1 - δ`. -/
theorem lemma_EC_1 {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) (X : ℕ → Ω → ℝ) (T : ℕ) (hT : 1 ≤ T) (b₁ b₂ : ℝ)
    (hb₁ : 1 ≤ b₁) (hb₂ : 0 < b₂)
    (hadapt : ∀ t < T, StronglyMeasurable[ℱ (t + 1)] (X t))
    (hint : ∀ t < T, Integrable (X t) μ)
    (hmds : ∀ t < T, μ[X t | ℱ t] =ᵐ[μ] 0)
    (htail : ∀ t < T, ∀ a : ℝ, 0 ≤ a →
      μ[{ω | a ≤ |X t ω|}.indicator (fun _ => (1 : ℝ)) | ℱ t]
        ≤ᵐ[μ] fun _ => 2 * b₁ * Real.exp (-b₂ * a ^ 2))
    (δ : ℝ) (hδ : 0 < δ) :
    μ {ω | Real.sqrt (28 * b₁ / (b₂ * T) * Real.log (1 / δ)) <
        (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, X t ω} ≤ ENNReal.ofReal δ := by sorry

end GradDOvS.Submod

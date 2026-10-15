-- Prove2me | Theorems.Thm_FreeSamples_Revenue_lemma_1_iii
-- name    : FreeSamples.Revenue.lemma_1_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T00:41:53.294721+00:00
-- url     : https://prove2.me/theorems/8e00ac95-c5dc-451e-86cc-32e661d7eb3c
-- title:
--   Lemma 1(iii), p. 14 — the second moment of the Buyer's belief increment is σ_t⁴/σ² dt + O(dt^{3/2}) for both parties
-- statement:
--   Let $\theta_h$ be the Buyer's posterior mean after $h$ samples. Under the Seller's model and under the Buyer's model, there is a constant $C$ such that for every $h\in(0,1]$
--   $$\Big|\,\mathbb E\big[(\theta_h-\theta_0)^2\big]-\frac{\sigma_0^4}{\sigma^2}h\,\Big|\le C\,h^{3/2}.$$
--
--   This is Lemma 1(iii), $\mathbb E^S_t[(d\theta_t)^2]=\mathbb E^B_t[(d\theta_t)^2]=\frac{\sigma_t^4}{\sigma^2}dt+O(dt^{3/2})$, at the initial state. The quadratic variation of the belief is the same for both parties, which is why the curvature term $\tfrac12 BR_{\theta\theta}$ enters both parts of Lemma 4 with the same coefficient.
--
--   **Formalization Note.** The $O(dt^{3/2})$ term is rendered with an explicit constant on $(0,1]$. The statement is posed at time $0$ for arbitrary parameters; see Lemma 1(ii).
-- source:
--   Drakopoulos & Makhdoumi, Providing Data Samples for Free, SSRN 3611003, p. 14, Lemma 1(iii)

import Mathlib
import Definitions.Def_FreeSamples_Revenue_Setting

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace FreeSamples.Revenue

universe u

theorem lemma_1_iii (p : Params) :
    (∃ C : ℝ, ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (θ : Ω → ℝ) (B : ℝ≥0 → Ω → ℝ),
      IsModel P (p.θ₀ + p.μb) p.σssq θ B →
      ∀ h ∈ Set.Ioc (0 : ℝ) 1,
        |(∫ ω, (p.buyerMean h (Y p.σsq θ B h.toNNReal ω) - p.θ₀) ^ 2 ∂P)
            - p.σ₀sq ^ 2 / p.σsq * h| ≤ C * h ^ ((3 : ℝ) / 2)) ∧
    (∃ C : ℝ, ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (θ : Ω → ℝ) (B : ℝ≥0 → Ω → ℝ),
      IsModel P p.θ₀ p.σ₀sq θ B →
      ∀ h ∈ Set.Ioc (0 : ℝ) 1,
        |(∫ ω, (p.buyerMean h (Y p.σsq θ B h.toNNReal ω) - p.θ₀) ^ 2 ∂P)
            - p.σ₀sq ^ 2 / p.σsq * h| ≤ C * h ^ ((3 : ℝ) / 2)) := by sorry

end FreeSamples.Revenue

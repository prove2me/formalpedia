-- Prove2me | Theorems.Thm_FreeSamples_Revenue_lemma_1_ii
-- name    : FreeSamples.Revenue.lemma_1_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T00:41:45.105047+00:00
-- url     : https://prove2.me/theorems/bb5ea03b-9732-4f4b-aa4a-ec012ea01c64
-- title:
--   Lemma 1(ii), p. 14 — the Buyer's estimate has zero drift for the Buyer and drift g_t σ_t²/σ² for the Seller
-- statement:
--   Let $\theta_h$ be the Buyer's posterior mean after $h$ samples (Proposition 1), a function of $Y_h=\theta h+\sigma B_h$.
--
--   1. Under the Buyer's model, $\theta\sim\mathcal N(\theta_0,\sigma_0^2)$, the map $h\mapsto\mathbb E[\theta_h]$ has right derivative $0$ at $h=0$.
--   2. Under the Seller's model, $\theta\sim\mathcal N(\theta_0+\mu_b,\sigma_s^2)$, it has right derivative
--   $$\frac{d}{dh}\Big|_{h=0^+}\mathbb E^S[\theta_h]=g_0\frac{\sigma_0^2}{\sigma^2}=\mu_b\frac{\sigma_0^2}{\sigma^2}.$$
--
--   This is Lemma 1(ii), $\mathbb E^B_t[d\theta_t]=0$ and $\mathbb E^S_t[d\theta_t]=g_t\frac{\sigma_t^2}{\sigma^2}dt$, at the initial state. The Buyer expects her belief not to move, while the Seller expects it to move toward her own estimate. That is the persuasion effect behind Theorem 1.
--
--   **Formalization Note.** The paper's "at any $t\ge0$" in $dt$-notation is posed at time $0$ for arbitrary parameters $(\theta_0,\mu_b,\sigma_0^2,\sigma_b^2,\sigma^2)$. The statement at a later $t$ is the same one started from the posterior state, by the Markov property, and is not posed separately. Here $g_0=\tilde\theta_0-\theta_0=\mu_b$ (p. 14).
-- source:
--   Drakopoulos & Makhdoumi, Providing Data Samples for Free, SSRN 3611003, p. 14, Lemma 1(ii); g_0 = µ_b, p. 14

import Mathlib
import Definitions.Def_FreeSamples_Revenue_Setting

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace FreeSamples.Revenue

universe u

theorem lemma_1_ii (p : Params) :
    (∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (θ : Ω → ℝ) (B : ℝ≥0 → Ω → ℝ),
      IsModel P p.θ₀ p.σ₀sq θ B →
      HasDerivWithinAt (fun h : ℝ => ∫ ω, p.buyerMean h (Y p.σsq θ B h.toNNReal ω) ∂P)
        0 (Set.Ici 0) 0) ∧
    (∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (θ : Ω → ℝ) (B : ℝ≥0 → Ω → ℝ),
      IsModel P (p.θ₀ + p.μb) p.σssq θ B →
      HasDerivWithinAt (fun h : ℝ => ∫ ω, p.buyerMean h (Y p.σsq θ B h.toNNReal ω) ∂P)
        (p.μb * p.σ₀sq / p.σsq) (Set.Ici 0) 0) := by sorry

end FreeSamples.Revenue

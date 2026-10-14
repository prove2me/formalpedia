-- Prove2me | Theorems.Thm_InfoRelaxTS_Gap_lemma_6
-- name    : InfoRelaxTS.Gap.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:31:25.823463+00:00
-- url     : https://prove2.me/theorems/7e3ca729-b2bf-4546-bce9-893a9ef95f7f
-- title:
--   Lemma 6, p. 69 — 𝔼[(max_{i≤n} μ̂_{a,i} − (μ̄_a + zσ_n))⁺] ≤ (σ_n/z)e^{−z²/2}
-- statement:
--   Consider the setting of Theorem 3 (as in Lemma 5), fix an arm $a$ and $n\ge0$, and put
--   $$\sigma_n=\sqrt{\frac{Ln}{\nu(\nu+n)}} .$$
--   Then for every $z>0$,
--   $$\mathbb E\Big[\Big(\max_{0\le i\le n}\hat\mu_{a,i}-(\bar\mu_a+z\sigma_n)\Big)^+\Big]\le\frac{\sigma_n}{z}\,e^{-z^2/2},$$
--   where $\hat\mu_{a,i}$ is the posterior predictive mean after $i$ rewards, $\bar\mu_a=\bar\mu_a(\xi_a,\nu)$, and the expectation is over the outcome law $\mathcal I(y)$.
--
--   This maximal form controls the IRS.V-Zero inner problem, whose first-action loss in Lemma 3 involves $\max_{0\le n\le T-1}\hat\mu_{a,n}$.
--
--   **Formalization Note** $(x)^+=\max(x,0)$ and the maximum over $0\le i\le n$ is a finite supremum. At $n=0$ both sides are $0$.
-- source:
--   Min, Maglaras, Moallemi, Thompson Sampling with Information Relaxation Penalties, arXiv:1902.04251v2, p. 69, Lemma 6, (234)

import Mathlib
import Definitions.Def_InfoRelaxTS_Gap_Setting

open MeasureTheory ProbabilityTheory

namespace InfoRelaxTS.Gap

theorem lemma_6 {K : ℕ} (M : NEFModel K) (L ν : ℝ) (ξ : Fin K → ℝ)
    (hnorm : IsNormalized M) (hsmooth : IsLSmooth M L)
    (hprior : ∀ b, IsProperPrior M b (ξ b, ν))
    (hint : ∀ b, Integrable (fun r : ℝ => r) (predLaw M b (ξ b, ν)))
    (a : Fin K) (n : ℕ) :
    ∀ z : ℝ, 0 < z →
      ∫ ω, max ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
            (fun i => muHat M (fun b => (ξ b, ν)) a i ω)
          - (muBar M a (ξ a, ν) + z * Real.sqrt (L * n / (ν * (ν + n))))) 0
        ∂(I M (fun b => (ξ b, ν)))
      ≤ Real.sqrt (L * n / (ν * (ν + n))) / z * Real.exp (-z ^ 2 / 2) := by sorry

end InfoRelaxTS.Gap

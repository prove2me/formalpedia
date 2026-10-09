-- Prove2me | Theorems.Thm_NonconvexSaddle_PSGD_lemma_24
-- name    : NonconvexSaddle.PSGD.lemma_24
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:16:24.50432+00:00
-- url     : https://prove2.me/theorems/0c8df892-ea29-4f1e-9b66-b8b46059d295
-- title:
--   Lemma 24 — improve or localize, for perturbed SGD
-- statement:
--   In the setting of Lemma 23 ($f$ satisfying Assumption A, $g$ satisfying Assumption B, $0<\eta\le1/\ell$, $r\ge0$, $\tilde\sigma^2=\sigma^2+r^2$), there is an absolute constant $c>0$ such that for all $t_0\ge0$, $t>0$ and $\iota>0$, with probability at least $1-8dt\,e^{-\iota}$, the PSGD run satisfies
--   $$\forall\,\tau\le t:\qquad \|x_{t_0+\tau}-x_{t_0}\|^2\le c\,\eta t\,\big[f(x_{t_0})-f(x_{t_0+\tau})+\eta\tilde\sigma^2(\eta\ell t+\iota)\big].$$
--
--   Over a short window the iterates either decrease the function value substantially or stay in a small ball around the starting point. The lemma is the basis of the localization step (Lemma 27) of the escape-from-saddle argument.
--
--   **Formalization Note** The absolute constant is quantified before every other object; $t_0=0$ is allowed.
-- source:
--   Jin, Netrapalli, Ge, Kakade, Jordan, On Nonconvex Optimization for Machine Learning: Gradients, Stochasticity, and Saddle Points, arXiv:1902.04811v2, p. 24, Lemma 24

import Mathlib
import Definitions.Def_NonconvexSaddle_PSGD_Setting

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace NonconvexSaddle.PSGD

/-- Lemma 24 (Improve or Localize; arXiv:1902.04811v2, App. B.2, p. 24), in the setting of
Lemma 23. -/
theorem lemma_24 :
    ∃ c : ℝ, 0 < c ∧ ∀ (d : ℕ) (Θ : Type) [MeasurableSpace Θ] (𝒟 : Measure Θ)
      [IsProbabilityMeasure 𝒟] (g : E d → Θ → E d) (f : E d → ℝ) (ℓ ρ σ η r ι : ℝ) (x₀ : E d)
      (t₀ t : ℕ),
      1 ≤ d → AssumptionA f ℓ ρ → AssumptionB f g 𝒟 σ → Measurable (Function.uncurry g) →
      0 < η → η ≤ 1 / ℓ → 0 ≤ r → 0 < t → 0 < ι →
      ENNReal.ofReal (1 - 8 * d * t * Real.exp (-ι)) ≤
        noiseLaw (d := d) 𝒟 r {ω | ∀ τ ≤ t,
          ‖psgd g η x₀ ω (t₀ + τ) - psgd g η x₀ ω t₀‖ ^ 2 ≤
            c * η * t * (f (psgd g η x₀ ω t₀) - f (psgd g η x₀ ω (t₀ + τ)) +
              η * (σ ^ 2 + r ^ 2) * (η * ℓ * t + ι))} := by sorry

end NonconvexSaddle.PSGD

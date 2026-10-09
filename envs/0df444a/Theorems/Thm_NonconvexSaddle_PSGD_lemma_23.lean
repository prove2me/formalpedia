-- Prove2me | Theorems.Thm_NonconvexSaddle_PSGD_lemma_23
-- name    : NonconvexSaddle.PSGD.lemma_23
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:16:22.038161+00:00
-- url     : https://prove2.me/theorems/2f35e38f-0430-4a70-b8d3-9bb75a7cd04a
-- title:
--   Lemma 23 — descent lemma for perturbed SGD
-- statement:
--   Let $f:\mathbb R^d\to\mathbb R$ ($d\ge1$) satisfy Assumption A with constants $\ell,\rho$, and let the stochastic gradient $g$ satisfy Assumption B with level $\sigma>0$ (with $g$ jointly measurable). Write $\tilde\sigma^2=\sigma^2+r^2$. There is an absolute constant $c>0$ such that for every step size $0<\eta\le1/\ell$, perturbation radius $r\ge0$, start point $x_0$, times $t_0\ge0$, $t>0$ and every $\iota>0$, the PSGD run $(x_t)$ of Algorithm 2 with parameters $(\eta,r)$ satisfies, with probability at least $1-4e^{-\iota}$,
--   $$f(x_{t_0+t})-f(x_{t_0})\le-\frac{\eta}{8}\sum_{i=0}^{t-1}\|\nabla f(x_{t_0+i})\|^2+c\,\eta\tilde\sigma^2(\eta\ell t+\iota).$$
--
--   The function value decreases in proportion to the squared gradients along the way, up to an error caused by the stochastic gradients and the perturbations. This is the first of the two engines of the proof of Theorem 16.
--
--   **Formalization Note** The absolute constant is quantified before every other object. The page writes "for any fixed $t,t_0,\iota>0$"; $t_0=0$ is allowed here (the paper's proof reduces to that case).
-- source:
--   Jin, Netrapalli, Ge, Kakade, Jordan, On Nonconvex Optimization for Machine Learning: Gradients, Stochasticity, and Saddle Points, arXiv:1902.04811v2, p. 23, Lemma 23

import Mathlib
import Definitions.Def_NonconvexSaddle_PSGD_Setting

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace NonconvexSaddle.PSGD

/-- Lemma 23 (Descent Lemma; arXiv:1902.04811v2, App. B.2, p. 23), for PSGD(η, r) with free
`η ≤ 1/ℓ` and `r`, and any start time `t₀ ≥ 0`. -/
theorem lemma_23 :
    ∃ c : ℝ, 0 < c ∧ ∀ (d : ℕ) (Θ : Type) [MeasurableSpace Θ] (𝒟 : Measure Θ)
      [IsProbabilityMeasure 𝒟] (g : E d → Θ → E d) (f : E d → ℝ) (ℓ ρ σ η r ι : ℝ) (x₀ : E d)
      (t₀ t : ℕ),
      1 ≤ d → AssumptionA f ℓ ρ → AssumptionB f g 𝒟 σ → Measurable (Function.uncurry g) →
      0 < η → η ≤ 1 / ℓ → 0 ≤ r → 0 < t → 0 < ι →
      ENNReal.ofReal (1 - 4 * Real.exp (-ι)) ≤
        noiseLaw (d := d) 𝒟 r {ω |
          f (psgd g η x₀ ω (t₀ + t)) - f (psgd g η x₀ ω t₀) ≤
            -(η / 8) * ∑ i ∈ Finset.range t, ‖gradient f (psgd g η x₀ ω (t₀ + i))‖ ^ 2 +
              c * η * (σ ^ 2 + r ^ 2) * (η * ℓ * t + ι)} := by sorry

end NonconvexSaddle.PSGD

-- Prove2me | Theorems.Thm_KeskinZeevi_SufficientConditions_sq_pricing_error_bound_A11
-- name    : KeskinZeevi.SufficientConditions.sq_pricing_error_bound_A11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T04:01:43.482611+00:00
-- url     : https://prove2.me/theorems/0378c7c0-32bf-4e05-88d0-eaf19436b736
-- title:
--   (A11) — squared pricing error bound under the information growth condition
-- statement:
--   Consider the single-product model with light-tailed i.i.d. noise, and fix $\kappa_0 > 0$. There exist a constant $K > 0$ and a natural number $N$ with the following property. Let $\theta \in \Theta$, and let $\pi$ be any pricing policy whose information metric satisfies $J_t \ge \kappa_0 \sqrt t$ almost surely for all $t \ge 2$. Then for every $t \ge \max\{N, 2\}$,
--   $$\mathbb{E}^\pi_\theta(\varphi(\theta) - p_{t+1})^2 \;\le\; \frac{K \log t}{\sqrt t} + 2\,\mathbb{E}^\pi_\theta(\varphi(\vartheta_t) - p_{t+1})^2 .$$
--
--   Once information accumulates at rate $\sqrt t$, the estimation part of the squared pricing error decays like $\log t/\sqrt t$. What remains is the deviation from greedy pricing.
--
--   **Formalization Note.** On the page, (A11) reads $\mathbb{E}^\pi_\theta(\varphi(\theta)-p_{t+1})^2 \le 4\tilde K_0 \log t/(\rho\kappa_0\sqrt t) + 2\mathbb{E}^\pi_\theta(\varphi(\vartheta_t)-p_{t+1})^2$ for $t \ge N$. Here $\tilde K_0 = (1+5k)K_0$, $K_0 = \max_{j}\max_{\theta\in\Theta}(\partial\varphi/\partial\theta_j)^2$, $\rho, k$ are the constants of Lemma 3, and $N$ is the smallest natural number with $kN\exp(-\tfrac12\rho\kappa_0\sqrt N) \le 1$. Since $\rho$ and $k$ are existential in Lemma 3, the formal statement abstracts $K = 4\tilde K_0/(\rho\kappa_0)$ and $N$ as existential constants. They are quantified after the model, the noise and $\kappa_0$, and before $\theta$, $\pi$ and $t$. This is the uniformity the paper's explicit constants have. Only condition (i) of Theorem 2 is assumed, stated from $t = 2$ on (see the goal theorem). $\log$ is the natural logarithm, which is positive for $t \ge 2$.
-- source:
--   Keskin and Zeevi, Dynamic Pricing with an Unknown Demand Model, Operations Research 62(5), 2014, p. 1158, Appendix A.2, proof of Theorem 2, Eq. (A11)

import Mathlib
import Definitions.Def_RobustBooking_Shared_Noise
import Definitions.Def_KeskinZeevi_SufficientConditions_LeastSquares
open RobustBooking.Shared

open MeasureTheory ProbabilityTheory

namespace KeskinZeevi.SufficientConditions

/-- Keskin–Zeevi 2014, p. 1158, (A11), with its constants abstracted: given `κ₀ > 0` there are
`K > 0` and `N` (the paper's `K = 4K̃₀/(ρκ₀)` and `N`, depending only on the model, the noise
law and `κ₀`) such that for every `θ ∈ Θ` and every policy with `J_t ≥ κ₀ √t` almost surely for
all `t ≥ 2`, and every `t ≥ max N 2`,
`E(φ(θ) - p_{t+1})² ≤ K log t / √t + 2 E(φ(ϑ_t) - p_{t+1})²`. -/
theorem sq_pricing_error_bound_A11 (M : Model) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ε : ℕ → Ω → ℝ) (σ : ℝ)
    (hε : LightTailedNoise P ε σ) (κ₀ : ℝ) (hκ₀ : 0 < κ₀) :
    ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ,
      ∀ (θ : ℝ × ℝ), θ ∈ M.Theta → ∀ π : Policy M,
        (∀ᵐ ω ∂P, ∀ t : ℕ, 2 ≤ t → κ₀ * Real.sqrt t ≤ infoMetric π θ ε t ω) →
        ∀ t : ℕ, N ≤ t → 2 ≤ t →
          ∫ ω, (phi θ - price π θ ε (t + 1) ω) ^ 2 ∂P ≤
            K * Real.log t / Real.sqrt t +
              2 * ∫ ω, (phi (truncEstimate π θ ε t ω) - price π θ ε (t + 1) ω) ^ 2 ∂P := by sorry

end KeskinZeevi.SufficientConditions

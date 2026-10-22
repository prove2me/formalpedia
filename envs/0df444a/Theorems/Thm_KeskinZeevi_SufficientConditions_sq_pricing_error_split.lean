-- Prove2me | Theorems.Thm_KeskinZeevi_SufficientConditions_sq_pricing_error_split
-- name    : KeskinZeevi.SufficientConditions.sq_pricing_error_split
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T04:01:42.836708+00:00
-- url     : https://prove2.me/theorems/d0e4a1a8-1070-40d3-b477-77a150b9b2f8
-- title:
--   (A10) — splitting the squared pricing error
-- statement:
--   For every pricing policy $\pi$, every $\theta \in \Theta$ and every $t \ge 2$,
--   $$\mathbb{E}^\pi_\theta(\varphi(\theta) - p_{t+1})^2 \;\le\; 2\,\mathbb{E}^\pi_\theta(\varphi(\theta) - \varphi(\vartheta_t))^2 + 2\,\mathbb{E}^\pi_\theta(\varphi(\vartheta_t) - p_{t+1})^2 .$$
--   Here $\vartheta_t$ is the truncated least squares estimate calculated at the end of period $t$, and $\varphi(\vartheta) = -\vartheta_1/(2\vartheta_2)$ is the myopic price.
--
--   This inequality separates the revenue loss of period $t+1$ into two parts: the estimation error and the deviation of the charged price from the greedy least squares price.
--
--   **Formalization Note.** Expectations are Bochner integrals over the noise space. Every integrand is measurable and bounded, since $p_{t+1} \in [l,u]$ and $\vartheta_t \in \Theta$ gives $\varphi(\vartheta_t) \in (l,u)$, so no integrability hypothesis is needed. The restriction $t \ge 2$ keeps $\vartheta_t$ the paper's object. The paper's $\vartheta_0$ and $\vartheta_1$ are not defined for a general policy.
-- source:
--   Keskin and Zeevi, Dynamic Pricing with an Unknown Demand Model, Operations Research 62(5), 2014, p. 1158, Appendix A.2, proof of Theorem 2, Eq. (A10)

import Mathlib
import Definitions.Def_RobustBooking_Shared_Noise
import Definitions.Def_KeskinZeevi_SufficientConditions_LeastSquares
open RobustBooking.Shared

open MeasureTheory ProbabilityTheory

namespace KeskinZeevi.SufficientConditions

/-- Keskin–Zeevi 2014, p. 1158, (A10): for every policy, every `θ ∈ Θ` and every `t ≥ 2`,
`E(φ(θ) - p_{t+1})² ≤ 2 E(φ(θ) - φ(ϑ_t))² + 2 E(φ(ϑ_t) - p_{t+1})²`, where `ϑ_t` is the truncated
least squares estimate at the end of period `t`. All integrands are bounded and measurable. -/
theorem sq_pricing_error_split (M : Model) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ε : ℕ → Ω → ℝ) (σ : ℝ)
    (hε : LightTailedNoise P ε σ) (π : Policy M) (θ : ℝ × ℝ) (hθ : θ ∈ M.Theta)
    (t : ℕ) (ht : 2 ≤ t) :
    ∫ ω, (phi θ - price π θ ε (t + 1) ω) ^ 2 ∂P ≤
      2 * ∫ ω, (phi θ - phi (truncEstimate π θ ε t ω)) ^ 2 ∂P +
        2 * ∫ ω, (phi (truncEstimate π θ ε t ω) - price π θ ε (t + 1) ω) ^ 2 ∂P := by sorry

end KeskinZeevi.SufficientConditions

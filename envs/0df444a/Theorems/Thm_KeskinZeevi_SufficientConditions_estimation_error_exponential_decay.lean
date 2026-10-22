-- Prove2me | Theorems.Thm_KeskinZeevi_SufficientConditions_estimation_error_exponential_decay
-- name    : KeskinZeevi.SufficientConditions.estimation_error_exponential_decay
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T04:01:21.224996+00:00
-- url     : https://prove2.me/theorems/b8b5a083-1937-4e04-be1c-f1540dcaf8a5
-- title:
--   Lemma 3 — exponential decay of least squares estimation errors
-- statement:
--   Consider the single-product model with light-tailed i.i.d. noise. There exist finite positive constants $\rho$ and $k$, depending only on the model and the noise law, with the following property. For every pricing policy $\pi$, every $\theta \in \Theta$, all $\delta, m > 0$ and all $t \ge 2$,
--   $$\mathbb{P}^\pi_\theta\big\{\lVert \hat\theta_t - \theta \rVert > \delta,\ J_t \ge m\big\} \;\le\; k\, t\, \exp\!\big(-\rho\,(\delta \wedge \delta^2)\, m\big).$$
--   Here $\hat\theta_t$ is the least squares estimate after $t$ periods, $J_t$ is the information metric, and $\lVert\cdot\rVert$ is the Euclidean norm.
--
--   The prices are chosen adaptively by the policy, so the estimation errors are not those of a fixed design. The lemma says that the policy controls the estimation accuracy through $J_t$ alone.
--
--   **Formalization Note.** The noise is `LightTailedNoise` (i.i.d., mean zero, variance $\sigma^2$, finite exponential moments near $0$), and $\mathbb{P}^\pi_\theta$ is realised on the noise space through the price process of `π`. The constants $\rho, k$ are quantified after the model and the noise and before $\pi$, $\theta$, $\delta$, $m$ and $t$, as on the page. On the event $J_t \ge m > 0$ the matrix $\mathcal{J}_t$ is invertible, so the junk value of `Matrix.inv` plays no role. The probability is an `ENNReal` bounded by `ENNReal.ofReal` of the right-hand side.
-- source:
--   Keskin and Zeevi, Dynamic Pricing with an Unknown Demand Model, Operations Research 62(5), 2014, p. 1147, Lemma 3, Eq. (15)

import Mathlib
import Definitions.Def_RobustBooking_Shared_Noise
import Definitions.Def_KeskinZeevi_SufficientConditions_LeastSquares
open RobustBooking.Shared

open MeasureTheory ProbabilityTheory

namespace KeskinZeevi.SufficientConditions

/-- Keskin–Zeevi 2014, p. 1147, Lemma 3 (15): there are constants `ρ, k > 0`, depending only on
the model and the noise law, such that for every policy `π`, every `θ ∈ Θ`, all `δ, m > 0` and
all `t ≥ 2`,
`P(‖θ̂_t - θ‖ > δ, J_t ≥ m) ≤ k t exp(-ρ (δ ∧ δ²) m)`, with `‖·‖` the Euclidean norm. -/
theorem estimation_error_exponential_decay (M : Model) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ε : ℕ → Ω → ℝ) (σ : ℝ)
    (hε : LightTailedNoise P ε σ) :
    ∃ ρ k : ℝ, 0 < ρ ∧ 0 < k ∧
      ∀ (π : Policy M) (θ : ℝ × ℝ), θ ∈ M.Theta →
      ∀ δ m : ℝ, 0 < δ → 0 < m → ∀ t : ℕ, 2 ≤ t →
        P {ω | δ < euclidNorm (lsEstimate π θ ε t ω - θ) ∧ m ≤ infoMetric π θ ε t ω} ≤
          ENNReal.ofReal (k * t * Real.exp (-(ρ * min δ (δ ^ 2) * m))) := by sorry

end KeskinZeevi.SufficientConditions

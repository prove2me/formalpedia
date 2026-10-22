-- Prove2me | Theorems.Thm_KeskinZeevi_IncumbentSufficient_estimation_error_exponential_decay
-- name    : KeskinZeevi.IncumbentSufficient.estimation_error_exponential_decay
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T14:45:27.983579+00:00
-- url     : https://prove2.me/theorems/f9e832e2-f503-4298-99ac-a55fa396bb7f
-- title:
--   Lemma 5 — exponential decay of estimation errors
-- statement:
--   Consider the incumbent price model with light-tailed i.i.d. demand shocks. There is a constant $\rho > 0$, depending only on the model and the law of the shocks, such that for every pricing policy $\pi$, every slope $\beta \in \mathfrak B$, all $\delta, m > 0$ and all $t \ge 2$,
--   $$\mathbb P^\pi_\beta\big\{ |\hat\beta_t - \beta| > \delta,\ \hat J_t \ge m \big\} \le 2 \exp\big(-\rho\, (\delta \wedge \delta^2)\, m\big).$$
--   Once the accumulated information $\hat J_t$ is large, the least squares slope estimate is accurate with exponentially high probability, whatever the policy did to accumulate that information.
--
--   **Formalization Note.** $\rho$ is chosen before the policy, the slope, $\delta$, $m$ and $t$, as on the page ("there exists … ρ such that, under any pricing policy π"). The probability is the measure of the set of noise realizations on which both events hold, as an `ENNReal` bounded by `ENNReal.ofReal`. On that set $\hat J_t \ge m > 0$, so $\hat\beta_t$ is the paper's estimate.
-- source:
--   Keskin and Zeevi, Dynamic Pricing with an Unknown Demand Model, Operations Research 62(5), 2014, p. 1150, Lemma 5, Eq. (28)

import Mathlib
import Definitions.Def_RobustBooking_Shared_Noise
import Definitions.Def_KeskinZeevi_IncumbentSufficient_LeastSquares
open RobustBooking.Shared

open MeasureTheory ProbabilityTheory

namespace KeskinZeevi.IncumbentSufficient

/-- Keskin–Zeevi 2014, p. 1150, Lemma 5 (28): there is a constant `ρ > 0`, depending only on the
model and the noise law, such that for every policy `π`, every `β ∈ 𝔅`, all `δ, m > 0` and all
`t ≥ 2`, `P(|β̂_t - β| > δ, Ĵ_t ≥ m) ≤ 2 exp(-ρ (δ ∧ δ²) m)`. -/
theorem estimation_error_exponential_decay (M : Model) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ε : ℕ → Ω → ℝ) (σ : ℝ)
    (hε : LightTailedNoise P ε σ) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ (π : Policy M) (β : ℝ), β ∈ M.B →
      ∀ δ m : ℝ, 0 < δ → 0 < m → ∀ t : ℕ, 2 ≤ t →
        P {ω | δ < |betaHat π β ε t ω - β| ∧ m ≤ Jhat π β ε t ω} ≤
          ENNReal.ofReal (2 * Real.exp (-(ρ * min δ (δ ^ 2) * m))) := by sorry

end KeskinZeevi.IncumbentSufficient

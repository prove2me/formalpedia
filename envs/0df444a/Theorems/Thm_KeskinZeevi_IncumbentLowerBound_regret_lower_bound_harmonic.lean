-- Prove2me | Theorems.Thm_KeskinZeevi_IncumbentLowerBound_regret_lower_bound_harmonic
-- name    : KeskinZeevi.IncumbentLowerBound.regret_lower_bound_harmonic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T14:03:44.656461+00:00
-- url     : https://prove2.me/theorems/6e332777-3839-41b3-a1e3-eed365805c0a
-- title:
--   Proof of Theorem 3 — worst-case regret bounded below by a harmonic sum
-- statement:
--   Consider the incumbent price model with i.i.d. $\mathcal N(0,\sigma^2)$ demand shocks. There exist positive constants $K_1$ and $K_2$, depending only on the model, with the following property. For every pricing policy $\pi$ and every horizon $T$,
--   $$\Delta^\pi(T) \;\ge\; K_1 \sum_{t=1}^{T-1} \frac{1}{K_2 + t} \;\ge\; c \sum_{t=1}^{T-1} \frac1t, \qquad c = \frac{K_1}{1 + K_2}.$$
--   In the paper, $K_1 = |b_{\max}| c_0/(u-l)^2$ and $K_2 = c_1/(u-l)^2$, where $c_0$ and $c_1$ are the constants of Lemma 4.
--
--   This is the second display of the proof of Theorem 3. Since the harmonic sum $\sum_{t=1}^{T-1} 1/t$ is at least $\log T$, it gives the logarithmic lower bound.
--
--   **Formalization Note.** The sums over $t = 1, \dots, T-1$ are Lean sums over $[1, T)$. $K_1$ and $K_2$ are chosen before the probability space, the noise, the policy and the horizon. The statement asserts the existence of such constants rather than fixing $c_0$ and $c_1$, because Lemma 4's constants are themselves existential.
-- source:
--   Keskin and Zeevi, Dynamic Pricing with an Unknown Demand Model, Operations Research 62(5), 2014, p. 1159, Section A.3, proof of Theorem 3, second display

import Mathlib
import Definitions.Def_KeskinZeevi_IncumbentLowerBound_Model
import Definitions.Def_KeskinZeevi_IncumbentLowerBound_Policy
import Definitions.Def_RobustBooking_Shared_GaussianNoise
import Definitions.Def_KeskinZeevi_IncumbentLowerBound_Regret
open RobustBooking.Shared
open MeasureTheory

namespace KeskinZeevi.IncumbentLowerBound

/-- Proof of Theorem 3, second display on p. 1159: with `K₁ = |b_max| c₀/(u − l)²` and
`K₂ = c₁/(u − l)²`, `Δ^π(T) ≥ K₁ Σ_{t=1}^{T−1} 1/(K₂ + t) ≥ c Σ_{t=1}^{T−1} 1/t` where
`c = K₁/(1 + K₂)`. The sums over `t = 1, …, T − 1` are over `Finset.Ico 1 T`. The constants
depend only on the model `M`. -/
theorem regret_lower_bound_harmonic (M : Model) :
    ∃ K₁ : ℝ, 0 < K₁ ∧ ∃ K₂ : ℝ, 0 < K₂ ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ε : ℕ → Ω → ℝ), GaussianNoise M.σ P ε →
      ∀ (π : Policy M.l M.u) (T : ℕ),
        K₁ / (1 + K₂) * ∑ t ∈ Finset.Ico 1 T, 1 / (t : ℝ)
            ≤ K₁ * ∑ t ∈ Finset.Ico 1 T, 1 / (K₂ + (t : ℝ)) ∧
          K₁ * ∑ t ∈ Finset.Ico 1 T, 1 / (K₂ + (t : ℝ)) ≤ worstRegret M P ε π T := by sorry

end KeskinZeevi.IncumbentLowerBound

-- Prove2me | Theorems.Thm_KeskinZeevi_IncumbentLowerBound_cumulative_pricing_error_lower_bound
-- name    : KeskinZeevi.IncumbentLowerBound.cumulative_pricing_error_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T14:03:20.718794+00:00
-- url     : https://prove2.me/theorems/ba24a1fd-0a68-4e01-a4a1-2872460ab385
-- title:
--   Lemma 4 — lower bound on cumulative pricing error (incumbent price problem)
-- statement:
--   Consider the incumbent price model, in which the incumbent price relation (18) holds and the demand shocks are i.i.d. $\mathcal N(0,\sigma^2)$. There exist finite positive constants $c_0$ and $c_1$, depending only on the model, with the following property. For every pricing policy $\pi$ and every horizon $T$,
--   $$\sup_{\beta \in \mathfrak B,\ \psi(\beta) \ne 0} \left\{ \sum_{t=2}^T \mathbb E^\pi_\beta (x_t - \psi(\beta))^2 \right\} \;\ge\; \sum_{t=2}^T \frac{c_0}{c_1 + \sup_{\beta\in\mathfrak B}\{\mathbb E^\pi_\beta[\hat J_{t-1}]\}}.$$
--   Here $x_t = p_t - \hat p$ is the price deviation, $\psi(\beta)$ is the optimal deviation, and $\hat J_t = \sum_{s=1}^t x_s^2$ is the information metric (24). The supremum on the left ranges over the slopes for which the incumbent price is not optimal. The supremum on the right ranges over all of $\mathfrak B$.
--
--   This is the incumbent price analog of Lemma 1. It says that the cumulative pricing error can be small only if information accumulates, and it is the step from which Theorem 3 follows.
--
--   **Formalization Note.** Lean period $t$ is the paper's period $t+1$. The paper's $\sum_{t=2}^T$ is the Lean sum over $t \in [1, T)$, and the paper's $\hat J_{t-1}$ in term $t$ is `expInfo … t`, which sums over Lean periods $0, \dots, t-1$. The constants are chosen before the probability space, the noise, the policy and the horizon, so they depend only on the model $(l, u, \hat p, \hat D, b_{\min}, b_{\max}, \sigma)$.
-- source:
--   Keskin and Zeevi, Dynamic Pricing with an Unknown Demand Model, Operations Research 62(5), 2014, p. 1149, Lemma 4

import Mathlib
import Definitions.Def_KeskinZeevi_IncumbentLowerBound_Model
import Definitions.Def_KeskinZeevi_IncumbentLowerBound_Policy
import Definitions.Def_RobustBooking_Shared_GaussianNoise
import Definitions.Def_KeskinZeevi_IncumbentLowerBound_Regret
open RobustBooking.Shared
open MeasureTheory

namespace KeskinZeevi.IncumbentLowerBound

/-- Lemma 4 (Lower Bound on Cumulative Pricing Error), p. 1149, Eq. (25). Lean period `t` is the
paper's period `t + 1`, so the paper's `Σ_{t=2}^T` is `Σ_{t ∈ [1, T)}` here, and the paper's
`Ĵ_{t−1}` for the deviation `x_t` is `expInfo … t` for the Lean deviation `dev … t`. The
left supremum ranges over `{β ∈ 𝔅 : ψ(β) ≠ 0}`, the right one over all of `𝔅`, as printed.
The constants depend only on the model `M`. -/
theorem cumulative_pricing_error_lower_bound (M : Model) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ c₁ : ℝ, 0 < c₁ ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ε : ℕ → Ω → ℝ), GaussianNoise M.σ P ε →
      ∀ (π : Policy M.l M.u) (T : ℕ),
        ∑ t ∈ Finset.Ico 1 T, c₀ / (c₁ + ⨆ β : M.B, expInfo M P ε π (β : ℝ) t)
          ≤ ⨆ β : M.Bexcl, ∑ t ∈ Finset.Ico 1 T, sqErr M P ε π (β : ℝ) t := by sorry

end KeskinZeevi.IncumbentLowerBound

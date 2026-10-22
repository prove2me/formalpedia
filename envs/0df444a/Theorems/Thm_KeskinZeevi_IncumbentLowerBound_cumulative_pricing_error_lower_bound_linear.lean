-- Prove2me | Theorems.Thm_KeskinZeevi_IncumbentLowerBound_cumulative_pricing_error_lower_bound_linear
-- name    : KeskinZeevi.IncumbentLowerBound.cumulative_pricing_error_lower_bound_linear
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T14:03:42.861344+00:00
-- url     : https://prove2.me/theorems/5b741ed1-6378-4d53-8a01-cb37b7ee1c99
-- title:
--   Proof of Theorem 3, first display — Lemma 4 with the information metric bounded by (u − l)²(t − 1)
-- statement:
--   Consider the incumbent price model with i.i.d. $\mathcal N(0,\sigma^2)$ demand shocks. There exist finite positive constants $c_0$ and $c_1$, depending only on the model, with the following property. For every pricing policy $\pi$ and every horizon $T$,
--   $$\sup_{\beta \in \mathfrak B,\ \psi(\beta) \ne 0} \left\{ \sum_{t=2}^T \mathbb E^\pi_\beta (x_t - \psi(\beta))^2 \right\} \;\ge\; \sum_{t=2}^T \frac{c_0}{c_1 + (u-l)^2 (t-1)}.$$
--
--   The paper derives it from Lemma 4 and the bound $\hat J_s \le (u-l)^2 s$ on the information metric, which holds because both the prices and the incumbent price lie in $[l,u]$. It is the first display of the proof of Theorem 3.
--
--   **Formalization Note.** Lean period $t$ is the paper's period $t+1$. For the paper's $t \in \{2, \dots, T\}$, the paper's $t-1$ is the Lean index $t \in [1, T)$ itself. The constants are chosen before the probability space, the noise, the policy and the horizon.
-- source:
--   Keskin and Zeevi, Dynamic Pricing with an Unknown Demand Model, Operations Research 62(5), 2014, p. 1158, Section A.3, proof of Theorem 3, first display

import Mathlib
import Definitions.Def_KeskinZeevi_IncumbentLowerBound_Model
import Definitions.Def_KeskinZeevi_IncumbentLowerBound_Policy
import Definitions.Def_RobustBooking_Shared_GaussianNoise
import Definitions.Def_KeskinZeevi_IncumbentLowerBound_Regret
open RobustBooking.Shared
open MeasureTheory

namespace KeskinZeevi.IncumbentLowerBound

/-- Proof of Theorem 3, first display (p. 1158): since `Ĵ_s ≤ (u − l)² s`, Lemma 4 gives
`sup_{β∈𝔅, ψ(β)≠0} Σ_{t=2}^T E^π_β(x_t − ψ(β))² ≥ Σ_{t=2}^T c₀ / (c₁ + (u − l)²(t − 1))`.
Lean period `t` is the paper's period `t + 1`; the paper's `t − 1` for `t ∈ [2, T]` is the Lean
index `t ∈ [1, T)` itself. The constants depend only on the model `M`. -/
theorem cumulative_pricing_error_lower_bound_linear (M : Model) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ c₁ : ℝ, 0 < c₁ ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ε : ℕ → Ω → ℝ), GaussianNoise M.σ P ε →
      ∀ (π : Policy M.l M.u) (T : ℕ),
        ∑ t ∈ Finset.Ico 1 T, c₀ / (c₁ + (M.u - M.l) ^ 2 * (t : ℝ))
          ≤ ⨆ β : M.Bexcl, ∑ t ∈ Finset.Ico 1 T, sqErr M P ε π (β : ℝ) t := by sorry

end KeskinZeevi.IncumbentLowerBound

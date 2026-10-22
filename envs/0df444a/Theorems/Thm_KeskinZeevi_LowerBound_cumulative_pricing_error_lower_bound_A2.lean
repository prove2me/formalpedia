-- Prove2me | Theorems.Thm_KeskinZeevi_LowerBound_cumulative_pricing_error_lower_bound_A2
-- name    : KeskinZeevi.LowerBound.cumulative_pricing_error_lower_bound_A2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T02:43:24.855105+00:00
-- url     : https://prove2.me/theorems/41427cfe-48e5-4538-acf7-5953de1ec1e7
-- title:
--   (A2) — Lemma 1 restated with cumulative squared pricing errors
-- statement:
--   In the single-product linear-demand model with parameter set $\Theta$ and i.i.d. $\mathcal{N}(0,\sigma^2)$ demand shocks, there exist finite positive constants $c_0$ and $c_1$ such that, for every pricing policy $\pi$ and every horizon $T$,
--   $$\sup_{\theta\in\Theta}\Big\{\sum_{t=2}^T \mathbb{E}^\pi_\theta(p_t-\varphi(\theta))^2\Big\} \;\ge\; \sum_{t=2}^T \frac{c_0}{c_1 + \sup_{\theta\in\Theta}\big\{\sum_{s=1}^{t-1}\mathbb{E}^\pi_\theta(p_s-\varphi(\theta))^2\big\}}.$$
--   This is inequality (A2), which the paper derives from Lemma 1 by the identity $C(\theta)\mathbb{E}^\pi_\theta[\mathcal{J}_{t-1}]C(\theta)^{\mathsf T} = \sum_{s=1}^{t-1}\mathbb{E}^\pi_\theta(p_s-\varphi(\theta))^2$. The same quantity appears on both sides, which is what forces $\sqrt{T}$ growth.
--
--   **Formalization Note.** $c_0, c_1$ depend only on the model and are chosen before the noise, the policy and the horizon. Paper periods $t = 2,\dots,T$ are Lean periods $1,\dots,T-1$. Paper periods $s = 1,\dots,t-1$ are Lean periods $0,\dots,t-2$ (`Finset.range` of the Lean index).
-- source:
--   Keskin and Zeevi, Dynamic Pricing with an Unknown Demand Model, Operations Research 62(5), 2014, p. 1156, Appendix A.1, proof of Theorem 1, Eq. (A2)

import Mathlib
import Definitions.Def_KeskinZeevi_LowerBound_Model
import Definitions.Def_KeskinZeevi_LowerBound_Policy
import Definitions.Def_RobustBooking_Shared_GaussianNoise
import Definitions.Def_KeskinZeevi_LowerBound_Regret
open RobustBooking.Shared
open MeasureTheory

namespace KeskinZeevi.LowerBound

/-- Inequality (A2) (Keskin and Zeevi 2014, §A.1, p. 1156), Lemma 1 with the quadratic form
written out: there are finite positive constants `c₀, c₁`, depending only on the model, such
that for every Gaussian noise sequence, every policy `π` and every horizon `T`,
`sup_{θ∈Θ} Σ_{t=2}^T E^π_θ(p_t − φ(θ))² ≥ Σ_{t=2}^T c₀ / (c₁ + sup_{θ∈Θ} Σ_{s=1}^{t−1} E^π_θ(p_s − φ(θ))²)`.
Paper periods `t = 2, …, T` are Lean periods `1, …, T − 1`; paper periods `s = 1, …, t − 1`
are Lean periods `0, …, t − 2`. -/
theorem cumulative_pricing_error_lower_bound_A2.{u} (M : Model) :
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ε : ℕ → Ω → ℝ), GaussianNoise M.σ P ε →
      ∀ (π : Policy M.l M.u) (T : ℕ),
        ∑ t ∈ Finset.Ico 1 T,
            c₀ / (c₁ + ⨆ θ : M.Θ, ∑ s ∈ Finset.range t, sqErr P ε π (θ : ℝ × ℝ) s)
          ≤ ⨆ θ : M.Θ, ∑ t ∈ Finset.Ico 1 T, sqErr P ε π (θ : ℝ × ℝ) t := by sorry

end KeskinZeevi.LowerBound

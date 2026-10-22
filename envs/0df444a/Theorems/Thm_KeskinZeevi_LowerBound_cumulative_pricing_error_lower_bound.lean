-- Prove2me | Theorems.Thm_KeskinZeevi_LowerBound_cumulative_pricing_error_lower_bound
-- name    : KeskinZeevi.LowerBound.cumulative_pricing_error_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T02:56:16.07268+00:00
-- url     : https://prove2.me/theorems/b3e819f1-c5f6-4b1f-8821-ca2b18cc98a1
-- title:
--   Lemma 1 — lower bound on cumulative pricing error
-- statement:
--   Consider the single-product linear-demand model with parameter set $\Theta$, price interval $[l,u]$ and i.i.d. $\mathcal{N}(0,\sigma^2)$ demand shocks. For a policy $\pi$ and $\theta \in \Theta$, let $p_t$ be the price in period $t$, let $\varphi(\theta)$ be the optimal price, and let $\mathcal{J}_t$ be the empirical Fisher information. Put $C(\theta) = [-\varphi(\theta)\ \ 1]$.
--
--   **Lemma 1.** There exist finite positive constants $c_0$ and $c_1$ such that, for every pricing policy $\pi$ and every horizon $T$,
--   $$\sup_{\theta\in\Theta}\Big\{\sum_{t=2}^T \mathbb{E}^\pi_\theta(p_t-\varphi(\theta))^2\Big\} \;\ge\; \sum_{t=2}^T \frac{c_0}{c_1 + \sup_{\theta\in\Theta}\{C(\theta)\,\mathbb{E}^\pi_\theta[\mathcal{J}_{t-1}]\,C(\theta)^{\mathsf T}\}}.$$
--
--   The lemma links how badly a policy prices to how much information it has gathered. It is the key step toward the $\sqrt{T}$ lower bound on regret (Theorem 1).
--
--   **Formalization Note.** The constants $c_0, c_1$ depend only on the model ($l,u,\Theta,\sigma$). In Lean they are chosen before the probability space, the noise, the policy and the horizon. The printed proof takes $c_0 = \sigma^2 l^2/(4 b_{\min}^2)$, which is positive only when $l>0$. The lemma still holds when $l=0$ with a different $c_0$, because $\varphi$ is positive and continuous on the compact set $\Theta$; so $l > 0$ is not assumed. Paper periods $t=2,\dots,T$ are Lean periods $1,\dots,T-1$ (`Finset.Ico 1 T`). The denominator term for Lean period $t$ uses $\mathcal{J}$ over the first $t$ periods, which is the paper's $\mathcal{J}_{t-1}$.
-- source:
--   Keskin and Zeevi, Dynamic Pricing with an Unknown Demand Model, Operations Research 62(5), 2014, p. 1146, Lemma 1, Eq. (14)

import Mathlib
import Definitions.Def_KeskinZeevi_LowerBound_Model
import Definitions.Def_KeskinZeevi_LowerBound_Policy
import Definitions.Def_RobustBooking_Shared_GaussianNoise
import Definitions.Def_KeskinZeevi_LowerBound_Regret
import Definitions.Def_KeskinZeevi_LowerBound_EmpiricalFisher
open RobustBooking.Shared
open MeasureTheory

namespace KeskinZeevi.LowerBound

/-- Lemma 1 (Keskin and Zeevi 2014, p. 1146, Eq. (14)). There are finite positive constants
`c₀, c₁`, depending only on the model, such that for every Gaussian noise sequence, every policy
`π` and every horizon `T`,
`sup_{θ∈Θ} Σ_{t=2}^T E^π_θ(p_t − φ(θ))² ≥ Σ_{t=2}^T c₀ / (c₁ + sup_{θ∈Θ} C(θ) E^π_θ[𝒥_{t−1}] C(θ)ᵀ)`.
Paper periods `t = 2, …, T` are Lean periods `1, …, T − 1`, and `infoQuad … t` is built from
`𝒥` over the first `t` periods, i.e. the paper's `𝒥_{t−1}` for paper period `t + 1`. -/
theorem cumulative_pricing_error_lower_bound.{u} (M : Model) :
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ε : ℕ → Ω → ℝ), GaussianNoise M.σ P ε →
      ∀ (π : Policy M.l M.u) (T : ℕ),
        ∑ t ∈ Finset.Ico 1 T, c₀ / (c₁ + ⨆ θ : M.Θ, infoQuad P ε π (θ : ℝ × ℝ) t)
          ≤ ⨆ θ : M.Θ, ∑ t ∈ Finset.Ico 1 T, sqErr P ε π (θ : ℝ × ℝ) t := by sorry

end KeskinZeevi.LowerBound

-- Prove2me | Theorems.Thm_KeskinZeevi_SufficientConditions_regret_eq_neg_beta_sum_sqErr
-- name    : KeskinZeevi.SufficientConditions.regret_eq_neg_beta_sum_sqErr
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T04:03:40.366283+00:00
-- url     : https://prove2.me/theorems/91d4fe37-4527-4065-985a-4af4caad9e0d
-- title:
--   Regret as a weighted sum of squared pricing errors
-- statement:
--   For every pricing policy $\pi$, every $\theta = (\alpha,\beta) \in \Theta$ and every horizon $T$,
--   $$\Delta^\pi_\theta(T) \;=\; -\beta \sum_{t=1}^{T} \mathbb{E}^\pi_\theta\big(p_t - \varphi(\theta)\big)^2 .$$
--   This holds because $r^*_\theta - r_\theta(p) = -\beta\,(p - \varphi(\theta))^2$ for the linear demand model. Since $b_{\min} \le \beta \le b_{\max} < 0$, the regret is at most $\lvert b_{\min}\rvert$ times the cumulative expected squared pricing error.
--
--   **Formalization Note.** The page displays this identity for the worst-case regret, $\Delta^\pi(T) = \sup_{\theta\in\Theta}\{-\beta\sum_{t=0}^{T-1}\mathbb{E}^\pi_\theta(\varphi(\theta)-p_{t+1})^2\}$. The formal statement is the per-$\theta$ identity inside the supremum, with the index shifted to $t = 1,\dots,T$. Expectations are integrals of bounded measurable functions over the noise space.
-- source:
--   Keskin and Zeevi, Dynamic Pricing with an Unknown Demand Model, Operations Research 62(5), 2014, p. 1158, Appendix A.2, proof of Theorem 2 (unnumbered display after (A11))

import Mathlib
import Definitions.Def_RobustBooking_Shared_Noise
import Definitions.Def_KeskinZeevi_SufficientConditions_Regret
open RobustBooking.Shared

open MeasureTheory ProbabilityTheory

namespace KeskinZeevi.SufficientConditions

/-- Keskin–Zeevi 2014, p. 1158, proof of Theorem 2 (unnumbered display): for every policy and
every `θ = (α, β) ∈ Θ`, `Δ^π_θ(T) = -β Σ_{t=1}^T E(p_t - φ(θ))²`. -/
theorem regret_eq_neg_beta_sum_sqErr (M : Model) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ε : ℕ → Ω → ℝ) (σ : ℝ)
    (hε : LightTailedNoise P ε σ) (π : Policy M) (θ : ℝ × ℝ) (hθ : θ ∈ M.Theta) (T : ℕ) :
    regret π θ ε P T =
      -θ.2 * ∑ t ∈ Finset.Icc 1 T, ∫ ω, (price π θ ε t ω - phi θ) ^ 2 ∂P := by sorry

end KeskinZeevi.SufficientConditions

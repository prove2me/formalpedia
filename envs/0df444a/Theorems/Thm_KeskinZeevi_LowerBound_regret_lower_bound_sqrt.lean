-- Prove2me | Theorems.Thm_KeskinZeevi_LowerBound_regret_lower_bound_sqrt
-- name    : KeskinZeevi.LowerBound.regret_lower_bound_sqrt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T02:44:08.699364+00:00
-- url     : https://prove2.me/theorems/dcd383ee-9419-473a-a714-39605ea915ad
-- title:
--   Theorem 1 — square-root lower bound on worst-case regret
-- statement:
--   A seller sets prices $p_t \in [l,u]$ ($0 \le l < u$) and observes demands $D_t = \alpha + \beta p_t + \varepsilon_t$. The shocks $\varepsilon_t$ are i.i.d. $\mathcal{N}(0,\sigma^2)$ with $\sigma>0$. The parameter $\theta=(\alpha,\beta)$ is unknown and lies in a rectangle $\Theta = [a_{\min},a_{\max}]\times[b_{\min},b_{\max}]$ with nonempty interior and $b_{\max}<0$. The optimal price $\varphi(\theta) = -\alpha/(2\beta)$ is interior to $[l,u]$ for every $\theta\in\Theta$. A pricing policy $\pi$ chooses each price as a measurable function of past demands and prices. Its worst-case regret is
--   $$\Delta^\pi(T) = \sup_{\theta\in\Theta}\Big\{T\,r_\theta(\varphi(\theta)) - \mathbb{E}^\pi_\theta\Big[\sum_{t=1}^T r_\theta(p_t)\Big]\Big\},\qquad r_\theta(p) = p(\alpha+\beta p).$$
--
--   **Theorem 1 (Lower Bound on Regret).** There exists a finite positive constant $c$ such that
--   $$\Delta^\pi(T) \;\ge\; c\sqrt{T}$$
--   for any pricing policy $\pi$ and time horizon $T \ge 3$.
--
--   So no policy can keep its worst-case regret below order $\sqrt{T}$ when both demand parameters are unknown. Policies whose regret grows no faster than $\sqrt{T}$, up to logarithmic factors, are therefore asymptotically optimal.
--
--   **Formalization Note.** The constant $c$ depends only on the model ($l, u, \Theta, \sigma$). In Lean it is chosen before the probability space, the noise, the policy and the horizon, and so it is uniform in all of them. The nonempty interior of $\Theta$ ($a_{\min}<a_{\max}$, $b_{\min}<b_{\max}$) is a standing assumption made explicit; the paper uses it through a prior density positive on the interior of $\Theta$. Policies are deterministic and non-anticipating, as in §2 of the paper.
-- source:
--   Keskin and Zeevi, Dynamic Pricing with an Unknown Demand Model, Operations Research 62(5), 2014, p. 1146, Theorem 1

import Mathlib
import Definitions.Def_KeskinZeevi_LowerBound_Model
import Definitions.Def_KeskinZeevi_LowerBound_Policy
import Definitions.Def_RobustBooking_Shared_GaussianNoise
import Definitions.Def_KeskinZeevi_LowerBound_Regret
open RobustBooking.Shared
open MeasureTheory

namespace KeskinZeevi.LowerBound

/-- Theorem 1 (Lower Bound on Regret; Keskin and Zeevi 2014, p. 1146). There is a finite
positive constant `c`, depending only on the model (`l`, `u`, `Θ`, `σ`), such that for every
sequence of i.i.d. `N(0, σ²)` demand shocks, every pricing policy `π` and every horizon
`T ≥ 3`, the worst-case regret satisfies `Δ^π(T) ≥ c √T`. -/
theorem regret_lower_bound_sqrt.{u} (M : Model) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ε : ℕ → Ω → ℝ), GaussianNoise M.σ P ε →
      ∀ (π : Policy M.l M.u) (T : ℕ), 3 ≤ T →
        c * Real.sqrt T ≤ worstRegret M P ε π T := by sorry

end KeskinZeevi.LowerBound

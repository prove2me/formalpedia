-- Prove2me | Theorems.Thm_KeskinZeevi_IncumbentLowerBound_regret_lower_bound_log
-- name    : KeskinZeevi.IncumbentLowerBound.regret_lower_bound_log
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T14:04:29.43865+00:00
-- url     : https://prove2.me/theorems/459f5fc3-31c0-4ce4-813e-25f904254bc4
-- title:
--   Theorem 3 — logarithmic lower bound on worst-case regret with a known incumbent price
-- statement:
--   Consider the incumbent price model of §3.4. Prices lie in $[l,u]$ with $0 \le l < u$. The seller knows an incumbent price $\hat p \in [l,u]$ and the incumbent demand $\hat D \ne 0$ at that price, so that $\hat D = \alpha + \beta\hat p$ (the incumbent price relation (18)). The unknown slope $\beta$ lies in $\mathfrak B = [b_{\min}, b_{\max}]$ with $b_{\min} < b_{\max} < 0$, and the optimal price is interior to $[l,u]$ for every $\beta \in \mathfrak B$. Demand in period $t$ is $D_t = \hat D + \beta x_t + \epsilon_t$, where $x_t = p_t - \hat p$ and the shocks $\epsilon_t$ are i.i.d. $\mathcal N(0, \sigma^2)$ with $\sigma > 0$.
--
--   **Theorem 3.** There exists a finite positive constant $c$ such that for every pricing policy $\pi$ and every horizon $T \ge 3$,
--   $$\Delta^\pi(T) \;\ge\; c \log T.$$
--   Here $\Delta^\pi(T) = \sup\{\Delta^\pi_\beta(T) : b_{\min} \le \beta \le b_{\max},\ \psi(\beta) \ne 0\}$ is the worst-case regret (22), and $\log$ is the natural logarithm.
--
--   Knowing the demand at one price lets the seller learn "for free" whenever it charges any other price, and the attainable regret drops from order $\sqrt T$ (Theorem 1) to order $\log T$. This theorem shows that $\log T$ cannot be beaten. Theorem 4 shows that it is achieved.
--
--   **Formalization Note.** The constant $c$ is chosen before the probability space, the noise, the policy and the horizon, so it depends only on the model $(l, u, \hat p, \hat D, b_{\min}, b_{\max}, \sigma)$. Policies are deterministic and non-anticipating, and their price process is generated from the noise by the recursion of the policy definition. The hypotheses $\hat p \in [l,u]$ and $\hat D \ne 0$ are fields of the model; they are implicit on the page, and without $\hat D \ne 0$ the theorem is false.
-- source:
--   Keskin and Zeevi, Dynamic Pricing with an Unknown Demand Model, Operations Research 62(5), 2014, p. 1149, Theorem 3

import Mathlib
import Definitions.Def_KeskinZeevi_IncumbentLowerBound_Model
import Definitions.Def_KeskinZeevi_IncumbentLowerBound_Policy
import Definitions.Def_RobustBooking_Shared_GaussianNoise
import Definitions.Def_KeskinZeevi_IncumbentLowerBound_Regret
open RobustBooking.Shared
open MeasureTheory

namespace KeskinZeevi.IncumbentLowerBound

/-- Theorem 3 (Lower Bound on Regret), p. 1149: under the incumbent price relation (18) there
is a finite positive constant `c`, depending only on the model `M` (price interval, incumbent
price and demand, slope interval, noise level), such that `Δ^π(T) ≥ c log T` for every pricing
policy `π` and every horizon `T ≥ 3`; `Δ^π(T)` is the worst-case regret (22) over
`{β ∈ 𝔅 : ψ(β) ≠ 0}`. -/
theorem regret_lower_bound_log (M : Model) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ε : ℕ → Ω → ℝ), GaussianNoise M.σ P ε →
      ∀ (π : Policy M.l M.u) (T : ℕ), 3 ≤ T →
        c * Real.log T ≤ worstRegret M P ε π T := by sorry

end KeskinZeevi.IncumbentLowerBound

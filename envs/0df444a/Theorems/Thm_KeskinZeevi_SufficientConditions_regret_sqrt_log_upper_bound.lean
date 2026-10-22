-- Prove2me | Theorems.Thm_KeskinZeevi_SufficientConditions_regret_sqrt_log_upper_bound
-- name    : KeskinZeevi.SufficientConditions.regret_sqrt_log_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T04:03:59.577827+00:00
-- url     : https://prove2.me/theorems/76c8e38d-e178-4509-b195-b9f4880bf9cd
-- title:
--   Theorem 2 — sufficient conditions for √T log T regret
-- statement:
--   Consider the single-product linear demand model $D_t = \alpha + \beta p_t + \varepsilon_t$. Prices lie in $[l,u]$, $\theta = (\alpha,\beta)$ lies in the rectangle $\Theta$ with $b_{\max} < 0$ and interior myopic prices, and the noise is light-tailed i.i.d. Assume $\theta \in \Theta$. Let $\kappa_0, \kappa_1$ be finite positive constants, and let $\pi$ be a pricing policy that satisfies, almost surely and for all $t \ge 2$,
--
--   1. $J_t \ge \kappa_0 \sqrt t$, and
--   2. $\displaystyle\sum_{s=2}^{t} \big(\varphi(\vartheta_s) - p_{s+1}\big)^2 \le \kappa_1 \sqrt t$.
--
--   Here $J_t = \sum_{s=1}^t (p_s - \bar p_t)^2$ is the information metric, $\vartheta_s$ is the truncated least squares estimate after $s$ periods, and $\varphi(\vartheta_s)$ is the greedy least squares price. Then there exists a finite positive constant $C$ such that
--   $$\Delta^\pi_\theta(T) \;\le\; C \sqrt T \log T \qquad \text{for all } T \ge 3 .$$
--
--   Condition 1 forces the policy to keep learning, and condition 2 keeps it close to greedy pricing. Together they give regret within a logarithmic factor of the $\sqrt T$ lower bound. The paper's constrained and decaying-perturbation ILS variants satisfy both conditions.
--
--   **Formalization Note.** This statement makes two **corrections** to the printed theorem. (a) The page asks for (i) and (ii) "almost surely for all $t$". At $t = 1$, (i) would require $J_1 = 0 \ge \kappa_0 > 0$, which is impossible, so read literally the theorem is vacuous. Both conditions are therefore required for $t \ge 2$, which is how the proof uses them and how the paper's examples satisfy them. (b) The page's sum in (ii) runs from $s = 0$, but $\vartheta_0$ and $\vartheta_1$ are undefined for a general policy, since $\mathcal{J}_0$ and $\mathcal{J}_1$ are singular. The sum starts at $s = 2$. Every policy satisfying the page's (ii) satisfies this one, so the theorem is not weakened. Condition (i) for all $t \ge 2$ makes $\mathcal{J}_t$ invertible for every $t \ge 2$, so the junk value of the matrix inverse never enters. The constant $C$ is quantified after $\theta$ and $\pi$, as on the page. The paper's proof gives $C = \max\{C_0, C_1\}$ with $C_0 = \lvert b_{\min}\rvert(u-l)^2 N$ and $C_1 = \lvert b_{\min}\rvert(8\tilde K_0\rho^{-1}\kappa_0^{-1} + 2\kappa_1)$, which is in fact uniform in $\theta$ and $\pi$. $\log$ is the natural logarithm, and regret is the per-$\theta$ regret $\Delta^\pi_\theta(T)$.
-- source:
--   Keskin and Zeevi, Dynamic Pricing with an Unknown Demand Model, Operations Research 62(5), 2014, p. 1147, Theorem 2 (conditions stated for t >= 2 and the sum in (ii) from s = 2; see Formalization Note)

import Mathlib
import Definitions.Def_RobustBooking_Shared_Noise
import Definitions.Def_KeskinZeevi_SufficientConditions_LeastSquares
import Definitions.Def_KeskinZeevi_SufficientConditions_Regret
open RobustBooking.Shared

open MeasureTheory ProbabilityTheory

namespace KeskinZeevi.SufficientConditions

/-- Keskin–Zeevi 2014, p. 1147, Theorem 2 (Sufficient Conditions for Asymptotic Optimality),
with conditions (i)–(ii) required for `t ≥ 2` and the sum in (ii) started at `s = 2` (the
printed "for all t" is unsatisfiable at `t = 1`, and `ϑ_0, ϑ_1` are undefined): if
(i) `J_t ≥ κ₀ √t` and (ii) `Σ_{s=2}^t (φ(ϑ_s) - p_{s+1})² ≤ κ₁ √t` hold almost surely for all
`t ≥ 2`, then `Δ^π_θ(T) ≤ C √T log T` for all `T ≥ 3`, for some finite `C > 0`. -/
theorem regret_sqrt_log_upper_bound (M : Model) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ε : ℕ → Ω → ℝ) (σ : ℝ)
    (hε : LightTailedNoise P ε σ) (θ : ℝ × ℝ) (hθ : θ ∈ M.Theta)
    (κ₀ κ₁ : ℝ) (hκ₀ : 0 < κ₀) (hκ₁ : 0 < κ₁) (π : Policy M)
    (hπ : ∀ᵐ ω ∂P, ∀ t : ℕ, 2 ≤ t →
      κ₀ * Real.sqrt t ≤ infoMetric π θ ε t ω ∧
        ∑ s ∈ Finset.Icc 2 t, (phi (truncEstimate π θ ε s ω) - price π θ ε (s + 1) ω) ^ 2 ≤
          κ₁ * Real.sqrt t) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℕ, 3 ≤ T → regret π θ ε P T ≤ C * Real.sqrt T * Real.log T := by sorry

end KeskinZeevi.SufficientConditions

-- Prove2me | Theorems.Thm_KeskinZeevi_IncumbentSufficient_regret_log_upper_bound
-- name    : KeskinZeevi.IncumbentSufficient.regret_log_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T14:46:19.713868+00:00
-- url     : https://prove2.me/theorems/b3e98738-dc1f-4eb5-9ea4-c43841573884
-- title:
--   Theorem 4 — sufficient conditions for logarithmic regret with a known incumbent price
-- statement:
--   Consider the incumbent price model with light-tailed i.i.d. demand shocks, and a true slope $\beta \in \mathfrak B = [b_{\min}, b_{\max}]$ whose optimal deviation from the incumbent price is nonzero, $\psi(\beta) \ne 0$. There is a threshold $\kappa_0' > 0$ such that for every $\kappa_0 \ge \kappa_0'$, every $\kappa_1 > 0$ and every start time $t_0 \ge 1$ there is a finite constant $C > 0$ with the following property. If a pricing policy $\pi$ satisfies, almost surely, for all $t \ge t_0$,
--   $$\text{(i)}\ \ \hat J_t \ge \kappa_0 \log t \qquad\text{and}\qquad \text{(ii)}\ \ \sum_{s=1}^{t} (\psi(b_s) - x_{s+1})^2 \le \kappa_1 \log t,$$
--   then its regret is logarithmic:
--   $$\Delta^\pi_\beta(T) \le C \log T \qquad \text{for all } T \ge 3 .$$
--   Condition (i) asks the policy to keep accumulating information at a logarithmic rate, and (ii) asks it to stay close to the greedy (certainty-equivalent) deviation $\psi(b_s)$. By Theorem 3 of the same paper, $\log T$ is the best possible order, so policies meeting (i)–(ii) are asymptotically optimal.
--
--   **Formalization Note.** This is a **corrected form** of the printed theorem, which reads "There exist finite positive constants $\kappa_0, \kappa_1$, and $C$ such that if $\pi$ … satisfies (i) … (ii) $\sum_{s=0}^t (\psi(b_s) - x_{s+1})^2 \le \kappa_1 \log t$ almost surely for all $t$, then …". Read literally, the existential $\kappa_0, \kappa_1$ make the statement vacuous (take $\kappa_0$ so large that (i) fails for every policy at $t = 2$). The proof on pp. 1159–1160 shows that any $\kappa_0$ above a threshold works, that $\kappa_1$ is arbitrary, and that the conditions are used only for large $t$. The Lean statement is that content, which implies the printed statement (take $\kappa_0 = \kappa_0'$, any $\kappa_1$, $t_0 = 1$). The sum in (ii) starts at $s = 1$, because $b_0$ is defined only for greedy ILS; this weakens the hypothesis. $b_s$ uses Lean's $a/0 = 0$ when $\hat J_s = 0$, which under (i) can only happen for $s < \max(t_0, 2)$. The constant $C$ is chosen before the policy and the horizon, as on the page; it may depend on the model, the noise law, $\beta$, $\kappa_0$, $\kappa_1$ and $t_0$. The regret is for the fixed true slope $\beta$, not the worst case (22).
-- source:
--   Keskin and Zeevi, Dynamic Pricing with an Unknown Demand Model, Operations Research 62(5), 2014, p. 1150, Theorem 4 (proof pp. 1159-1160, Appendix A.3)

import Mathlib
import Definitions.Def_RobustBooking_Shared_Noise
import Definitions.Def_KeskinZeevi_IncumbentSufficient_LeastSquares
import Definitions.Def_KeskinZeevi_IncumbentSufficient_Regret
open RobustBooking.Shared

open MeasureTheory ProbabilityTheory

namespace KeskinZeevi.IncumbentSufficient

/-- Keskin–Zeevi 2014, p. 1150, Theorem 4 (Sufficient Conditions for Asymptotic Optimality), in
the form its proof establishes (the printed "there exist κ₀, κ₁" makes a literal reading
vacuous): for `β ∈ 𝔅` with `ψ(β) ≠ 0` there is a threshold `κ₀' > 0` such that for every
`κ₀ ≥ κ₀'`, every `κ₁ > 0` and every start time `t₀ ≥ 1` there is a finite `C > 0` with the
following property. If a policy `π` satisfies, almost surely for all `t ≥ t₀`,
(i) `Ĵ_t ≥ κ₀ log t` and (ii) `Σ_{s=1}^t (ψ(b_s) - x_{s+1})² ≤ κ₁ log t`, then
`Δ^π_β(T) ≤ C log T` for all `T ≥ 3`. `C` does not depend on `π` or `T`. -/
theorem regret_log_upper_bound (M : Model) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ε : ℕ → Ω → ℝ) (σ : ℝ)
    (hε : LightTailedNoise P ε σ) (β : ℝ) (hβ : β ∈ M.B) (hψ : M.psi β ≠ 0) :
    ∃ κ₀' : ℝ, 0 < κ₀' ∧ ∀ κ₀ : ℝ, κ₀' ≤ κ₀ → ∀ κ₁ : ℝ, 0 < κ₁ → ∀ t₀ : ℕ, 1 ≤ t₀ →
      ∃ C : ℝ, 0 < C ∧ ∀ π : Policy M,
        (∀ᵐ ω ∂P, ∀ t : ℕ, t₀ ≤ t →
          κ₀ * Real.log t ≤ Jhat π β ε t ω ∧
            ∑ s ∈ Finset.Icc 1 t, (M.psi (truncEst π β ε s ω) - dev π β ε (s + 1) ω) ^ 2 ≤
              κ₁ * Real.log t) →
        ∀ T : ℕ, 3 ≤ T → regret π β ε P T ≤ C * Real.log T := by sorry

end KeskinZeevi.IncumbentSufficient

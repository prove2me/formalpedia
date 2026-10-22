-- Prove2me | Theorems.Thm_KeskinZeevi_IncumbentSufficient_Jhat_linear_growth_on_goodEvent
-- name    : KeskinZeevi.IncumbentSufficient.Jhat_linear_growth_on_goodEvent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T14:45:57.15848+00:00
-- url     : https://prove2.me/theorems/22b68407-61a0-4d08-841a-4c08393ebc21
-- title:
--   Proof of Theorem 4 — linear growth of Ĵ_t on the event A_t
-- statement:
--   Fix a pricing policy, a slope $\beta$, a constant $\kappa_1$, a period $t \ge 3$ and a realization of the shocks. Suppose that condition (ii) of Theorem 4 holds at time $t - 1$ along this realization:
--   $$\sum_{s=1}^{t-1} (\psi(b_s) - x_{s+1})^2 \le \kappa_1 \log(t-1).$$
--   If the realization lies in the event $A_t$ (the greedy deviations $\psi(b_s)$ for $\lfloor (t-1)/2\rfloor \le s \le t-1$ are all within $|\psi(\beta)|/\sqrt{12}$ of $\psi(\beta)$), then
--   $$\hat J_t \ge \Big( \frac{(\psi(\beta))^2}{8} - \frac{\kappa_1 \log(t-1)}{t-1} \Big)(t-1).$$
--   So the information metric grows linearly in $t$ on $A_t$ when $\psi(\beta) \ne 0$: a policy that tracks the greedy price, which is bounded away from the uninformative incumbent price, accumulates information at a constant rate.
--
--   **Formalization Note.** The statement is deterministic (pathwise). The paper applies it for $t \ge N(\beta) \ge 5$; it is stated here for $t \ge 3$, where $\lfloor (t-1)/2 \rfloor \ge 1$ so that the sum in (ii) starts at $s = 1$ and covers every index of $A_t$. The sum in condition (ii) starts at $s = 1$ rather than the paper's $s = 0$, because $b_0$ is defined only for greedy ILS. $\log$ is the natural logarithm, applied to the real number $t - 1 \ge 2$.
-- source:
--   Keskin and Zeevi, Dynamic Pricing with an Unknown Demand Model, Operations Research 62(5), 2014, p. 1159, Appendix A.3, proof of Theorem 4, first display after Eq. (A16) (with the events A_t of Eq. (A15))

import Mathlib
import Definitions.Def_KeskinZeevi_IncumbentSufficient_LeastSquares

namespace KeskinZeevi.IncumbentSufficient

/-- Keskin–Zeevi 2014, p. 1159, proof of Theorem 4, display after (A16): pathwise, for `t ≥ 3`,
if condition (ii) holds at time `t - 1`, i.e. `Σ_{s=1}^{t-1} (ψ(b_s) - x_{s+1})² ≤ κ₁ log(t - 1)`,
then on the event `A_t` of (A15)
`Ĵ_t ≥ (ψ(β)²/8 - κ₁ log(t - 1)/(t - 1)) (t - 1)`. -/
theorem Jhat_linear_growth_on_goodEvent (M : Model) {Ω : Type*} (π : Policy M) (β : ℝ)
    (ε : ℕ → Ω → ℝ) (κ₁ : ℝ) (t : ℕ) (ht : 3 ≤ t) (ω : Ω)
    (hii : ∑ s ∈ Finset.Icc 1 (t - 1),
        (M.psi (truncEst π β ε s ω) - dev π β ε (s + 1) ω) ^ 2 ≤ κ₁ * Real.log ((t : ℝ) - 1))
    (hA : ω ∈ goodEvent π β ε t) :
    (M.psi β ^ 2 / 8 - κ₁ * Real.log ((t : ℝ) - 1) / ((t : ℝ) - 1)) * ((t : ℝ) - 1) ≤
      Jhat π β ε t ω := by sorry

end KeskinZeevi.IncumbentSufficient

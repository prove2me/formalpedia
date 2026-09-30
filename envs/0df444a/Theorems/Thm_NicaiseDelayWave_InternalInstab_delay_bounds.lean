-- Prove2me | Theorems.Thm_NicaiseDelayWave_InternalInstab_delay_bounds
-- name    : NicaiseDelayWave.InternalInstab.delay_bounds
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T22:30:05.815242+00:00
-- url     : https://prove2.me/theorems/f4fd73a4-9ba1-41ef-8c6e-c6b9b63fb919
-- title:
--   §5.2, p. 1585 — two-sided bounds on the destabilizing delays τ_{n,l} (corrected)
-- statement:
--   Let $0 < \mu_1 < \mu_2$, $l \in \mathbb N$, $\Lambda > 0$, $0 < \alpha < \tfrac12(\mu_2 - \mu_1)$ and $\tau > 0$ with
--   $$\alpha^2 + \frac{(2l+1)^2\pi^2}{\tau^2} = \Lambda^2 .$$
--   Then
--   1. $\displaystyle \tau > \frac{(2l+1)\pi}{\Lambda}$;
--   2. if moreover $\Lambda^2 > \tfrac14(\mu_2 - \mu_1)^2$, then
--   $$\tau < \frac{(2l+1)\pi}{\sqrt{\Lambda^2 - \tfrac14(\mu_2-\mu_1)^2}} .$$
--
--   Applied to the delays $\tau_{n,l}$ of Case (b), bound 1 shows $\tau_{n,l} \to +\infty$ as $l \to \infty$ for a fixed eigenvalue $\Lambda_n^2$, and bound 2 shows $\tau_{n,l} \to 0^+$ as $\Lambda_n \to \infty$ for a fixed $l$: the destabilizing delays are arbitrarily large and arbitrarily small.
--
--   **Formalization Note** The paper derives both limits from the single inequality $(2l+1)^2\pi^2/\tau_{n,l}^2 \le \Lambda_n^2$, which bounds $\tau_{n,l}$ only from below and so gives only the limit $l \to \infty$. The upper bound 2, which uses $\alpha < \tfrac12(\mu_2 - \mu_1)$, is the step needed for $\tau_{n,l} \to 0^+$; the statement includes it as the corrected form of the page's argument.
-- source:
--   Nicaise, Pignotti, Stability and Instability Results of the Wave Equation with a Delay Term in the Boundary or Internal Feedbacks, SIAM J. Control Optim. 45 (2006), p. 1585, §5.2 (bound on τ_{n,l} from the first equation of (5.25))

import Mathlib

namespace NicaiseDelayWave.InternalInstab

/-- Nicaise–Pignotti, §5.2, p. 1585 (corrected): if `0 < μ₁ < μ₂`, `α ∈ (0, (μ₂ − μ₁)/2)`,
`Λ > 0`, `τ > 0` and `α² + (2l+1)²π²/τ² = Λ²`, then `(2l+1)π/Λ < τ`, and if moreover
`(μ₂ − μ₁)²/4 < Λ²` then `τ < (2l+1)π / √(Λ² − (μ₂ − μ₁)²/4)`. -/
theorem delay_bounds (μ₁ μ₂ α τ Λ : ℝ) (l : ℕ) (hμ₁ : 0 < μ₁) (hμ : μ₁ < μ₂)
    (hα₀ : 0 < α) (hα₁ : α < (μ₂ - μ₁) / 2) (hΛ : 0 < Λ) (hτ : 0 < τ)
    (h : α ^ 2 + (2 * l + 1) ^ 2 * Real.pi ^ 2 / τ ^ 2 = Λ ^ 2) :
    (2 * l + 1) * Real.pi / Λ < τ ∧
      ((μ₂ - μ₁) ^ 2 / 4 < Λ ^ 2 →
        τ < (2 * l + 1) * Real.pi / Real.sqrt (Λ ^ 2 - (μ₂ - μ₁) ^ 2 / 4)) := by sorry

end NicaiseDelayWave.InternalInstab

-- Prove2me | Theorems.Thm_GoldenRatioVI_Explicit_step_estimates
-- name    : GoldenRatioVI.Explicit.step_estimates
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:29:41.763398+00:00
-- url     : https://prove2.me/theorems/95115e0b-03ae-4c13-ad2c-82ea6a3e14a9
-- title:
--   Eq. (18) — the two key estimations produced by the step rule (15)
-- statement:
--   Consider a run of Algorithm 1 (EGRAAL) with parameter $\phi\in(1,\varphi]$, stepsizes $(\lambda_k)$, ratios $(\theta_k)$ and iterates $(z^k)$. For every $k\ge 1$:
--
--   1. $\lambda_k\le\lambda_{k-1}\big(\frac1\phi+\frac1{\phi^2}\big)$;
--   2. $\theta_k\le 1+\frac1\phi$;
--   3. $$\lambda_k^2\,\|F(z^k)-F(z^{k-1})\|^2 \le \frac{\theta_k\theta_{k-1}}{4}\,\|z^k-z^{k-1}\|^2. \tag{18}$$
--
--   No assumption on $g$ or $F$ is needed: these are consequences of the step rule (15) and the update of $\theta_k$ alone. They replace the global Lipschitz constant in the convergence analysis.
-- source:
--   Malitsky, Golden Ratio Algorithms for Variational Inequalities, preprint (Optimization Online 6598, 2018), p. 5, Eq. (18) and the preceding sentence

import Mathlib
import Definitions.Def_GoldenRatioVI_Explicit_egraalRun

namespace GoldenRatioVI.Explicit

/-- Eq. (18) of Malitsky (p. 5), the two key estimations produced by the step rule (15):
for every `k ≥ 1`, `λ_k ≤ λ_{k−1}(1/ϕ + 1/ϕ²)`, hence `θ_k ≤ 1 + 1/ϕ`, and
`λ_k² ‖F(z^k) − F(z^{k−1})‖² ≤ (θ_k θ_{k−1} / 4) ‖z^k − z^{k−1}‖²`. -/
theorem step_estimates {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (g : E → EReal) (F : E → E) (ϕ lamBar : ℝ)
    (z zbar : ℕ → E) (lam theta : ℕ → ℝ)
    (hrun : IsEGRAALRun g F ϕ lamBar z zbar lam theta) (k : ℕ) (hk : 1 ≤ k) :
    lam k ≤ lam (k - 1) * (1 / ϕ + 1 / ϕ ^ 2) ∧
    theta k ≤ 1 + 1 / ϕ ∧
    lam k ^ 2 * ‖F (z k) - F (z (k - 1))‖ ^ 2 ≤
      theta k * theta (k - 1) / 4 * ‖z k - z (k - 1)‖ ^ 2 := by sorry

end GoldenRatioVI.Explicit

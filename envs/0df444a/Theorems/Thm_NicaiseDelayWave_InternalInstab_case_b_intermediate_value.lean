-- Prove2me | Theorems.Thm_NicaiseDelayWave_InternalInstab_case_b_intermediate_value
-- name    : NicaiseDelayWave.InternalInstab.case_b_intermediate_value
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T22:11:18.906872+00:00
-- url     : https://prove2.me/theorems/5fd4d4ba-bbc1-4983-907d-47e3f0a888c4
-- title:
--   (5.26)–(5.27), Case (b) μ2 > μ1 — for every Λ > 0 and l ∈ ℕ some α ∈ (0, (μ2−μ1)/2) solves (5.25) with τ = τ(α)
-- statement:
--   Let $0 < \mu_1 < \mu_2$, $l \in \mathbb N$ and $\Lambda > 0$. For $\alpha > 0$ put
--   $$\tau(\alpha) = \frac1\alpha \ln\Big(\frac{\mu_2}{\mu_1 + 2\alpha}\Big). \tag{5.26}$$
--   Then there exists $\alpha$ with $0 < \alpha < \tfrac12(\mu_2 - \mu_1)$ such that $\tau(\alpha) > 0$,
--   $$\mu_2 e^{-\alpha\tau(\alpha)} = 2\alpha + \mu_1, \qquad \alpha^2 + \frac{(2l+1)^2\pi^2}{\tau^2(\alpha)} = \Lambda^2. \tag{5.27}$$
--
--   Together with $\beta = (2l+1)\pi/\tau(\alpha)$ this gives a solution of (5.24)–(5.25) with $\alpha > 0$, hence a root $\lambda = \alpha + i\beta$ of (5.23) with positive real part, for every eigenvalue $\Lambda^2$ and every $l$.
-- source:
--   Nicaise, Pignotti, Stability and Instability Results of the Wave Equation with a Delay Term in the Boundary or Internal Feedbacks, SIAM J. Control Optim. 45 (2006), p. 1584, §5.2, Case (b), (5.26)–(5.27)

import Mathlib

namespace NicaiseDelayWave.InternalInstab

/-- Nicaise–Pignotti, §5.2, p. 1584, (5.26)–(5.27), Case (b): if `0 < μ₁ < μ₂`, `l ∈ ℕ` and
`Λ > 0`, there is `α ∈ (0, (μ₂ − μ₁)/2)` such that the delay `τ(α) = (1/α) ln(μ₂/(μ₁ + 2α))`
is positive, satisfies `μ₂e^{−ατ(α)} = 2α + μ₁`, and `α² + (2l+1)²π²/τ(α)² = Λ²` (5.27). -/
theorem case_b_intermediate_value (μ₁ μ₂ Λ : ℝ) (l : ℕ) (hμ₁ : 0 < μ₁) (hμ : μ₁ < μ₂)
    (hΛ : 0 < Λ) :
    ∃ α : ℝ, 0 < α ∧ α < (μ₂ - μ₁) / 2 ∧
      0 < Real.log (μ₂ / (μ₁ + 2 * α)) / α ∧
      μ₂ * Real.exp (-α * (Real.log (μ₂ / (μ₁ + 2 * α)) / α)) = 2 * α + μ₁ ∧
      α ^ 2 + (2 * l + 1) ^ 2 * Real.pi ^ 2 / (Real.log (μ₂ / (μ₁ + 2 * α)) / α) ^ 2
        = Λ ^ 2 := by sorry

end NicaiseDelayWave.InternalInstab

-- Prove2me | Theorems.Thm_NicaiseDelayWave_InternalInstab_case_a_equal_coefficients
-- name    : NicaiseDelayWave.InternalInstab.case_a_equal_coefficients
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T22:02:06.123896+00:00
-- url     : https://prove2.me/theorems/522167ed-b73f-403d-8707-e39745de924c
-- title:
--   §5.2 Case (a), μ1 = μ2 — the system (5.25) forces α = 0 and β² = Λ²
-- statement:
--   Let $\mu > 0$ and $\tau > 0$, and let $\alpha, \beta, \Lambda \in \mathbb R$ satisfy system (5.25) with $\mu_1 = \mu_2 = \mu$:
--   $$\alpha^2 + \beta^2 = \Lambda^2, \qquad \mu e^{-\alpha\tau} = 2\alpha + \mu .$$
--   Then
--   $$\alpha = 0 \qquad\text{and}\qquad \beta^2 = \Lambda^2 .$$
--
--   In the borderline case $\mu_1 = \mu_2$ the roots of (5.23) produced by (5.24) are purely imaginary, $\lambda = i\beta$ with $\beta^2 = \Lambda^2$; the corresponding solutions $e^{i\beta t}\varphi(x)$ have constant energy, and the delays are $\tau_{n,l} = (2l+1)\pi/\beta_n$.
-- source:
--   Nicaise, Pignotti, Stability and Instability Results of the Wave Equation with a Delay Term in the Boundary or Internal Feedbacks, SIAM J. Control Optim. 45 (2006), pp. 1583–1584, §5.2, Case (a)

import Mathlib

namespace NicaiseDelayWave.InternalInstab

/-- Nicaise–Pignotti, §5.2, pp. 1583–1584, Case (a): if `μ₁ = μ₂ = μ > 0` and `τ > 0`, the real
system (5.25) forces `α = 0` and `β² = Λ²`. -/
theorem case_a_equal_coefficients (μ τ α β Λ : ℝ) (hμ : 0 < μ) (hτ : 0 < τ)
    (h₁ : α ^ 2 + β ^ 2 = Λ ^ 2) (h₂ : μ * Real.exp (-α * τ) = 2 * α + μ) :
    α = 0 ∧ β ^ 2 = Λ ^ 2 := by sorry

end NicaiseDelayWave.InternalInstab

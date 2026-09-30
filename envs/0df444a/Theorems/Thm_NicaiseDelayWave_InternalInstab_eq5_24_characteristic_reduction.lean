-- Prove2me | Theorems.Thm_NicaiseDelayWave_InternalInstab_eq5_24_characteristic_reduction
-- name    : NicaiseDelayWave.InternalInstab.eq5_24_characteristic_reduction
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T21:56:16.957304+00:00
-- url     : https://prove2.me/theorems/455fa043-4081-4a98-ae96-2048fbe544e9
-- title:
--   (5.24)–(5.25) — with βτ = (2l+1)π the characteristic equation (5.23) reduces to a real system
-- statement:
--   Let $\alpha, \beta, \tau, \mu_1, \mu_2, \Lambda \in \mathbb R$ and $l \in \mathbb N$ with
--   $$\beta\tau = (2l+1)\pi. \tag{5.24}$$
--   Put $\lambda = \alpha + i\beta$. Then
--   $$\lambda^2 + \big(\mu_1 + \mu_2 e^{-\lambda\tau}\big)\lambda = -\Lambda^2 \quad\Longleftrightarrow\quad \begin{cases} \alpha^2 + \beta^2 = \Lambda^2, \\ \mu_2 e^{-\alpha\tau} = 2\alpha + \mu_1. \end{cases} \tag{5.25}$$
--
--   Under the choice (5.24) the factor $e^{-i\beta\tau}$ equals $-1$, and the complex equation (5.23) becomes two real equations; this is how §5.2 finds roots of (5.23).
--
--   **Formalization Note** The paper states the direction "(5.23) becomes (5.25)"; both directions hold because (5.24) forces $\beta \neq 0$, and the direction (5.25) ⇒ (5.23) is the one the construction uses. $\mathbb N$ contains $0$. No sign assumptions on $\tau, \mu_1, \mu_2$ are needed.
-- source:
--   Nicaise, Pignotti, Stability and Instability Results of the Wave Equation with a Delay Term in the Boundary or Internal Feedbacks, SIAM J. Control Optim. 45 (2006), p. 1583, §5.2, (5.24)–(5.25)

import Mathlib

namespace NicaiseDelayWave.InternalInstab

/-- Nicaise–Pignotti, §5.2, p. 1583, (5.24)–(5.25): if `λ = α + iβ` with `βτ = (2l+1)π`, then the
characteristic equation (5.23) `λ² + (μ₁ + μ₂e^{−λτ})λ = −Λ²` is equivalent to the real system
(5.25): `α² + β² = Λ²` and `μ₂e^{−ατ} = 2α + μ₁`. -/
theorem eq5_24_characteristic_reduction (α β τ μ₁ μ₂ Λ : ℝ) (l : ℕ)
    (hβτ : β * τ = (2 * l + 1) * Real.pi) :
    ((⟨α, β⟩ : ℂ) ^ 2 + ((μ₁ : ℂ) + (μ₂ : ℂ) * Complex.exp (-(⟨α, β⟩ : ℂ) * τ)) * ⟨α, β⟩
        = -((Λ : ℂ) ^ 2)) ↔
      (α ^ 2 + β ^ 2 = Λ ^ 2 ∧ μ₂ * Real.exp (-α * τ) = 2 * α + μ₁) := by sorry

end NicaiseDelayWave.InternalInstab

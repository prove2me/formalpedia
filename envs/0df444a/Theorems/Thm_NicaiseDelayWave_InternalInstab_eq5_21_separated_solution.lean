-- Prove2me | Theorems.Thm_NicaiseDelayWave_InternalInstab_eq5_21_separated_solution
-- name    : NicaiseDelayWave.InternalInstab.eq5_21_separated_solution
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T21:49:14.518577+00:00
-- url     : https://prove2.me/theorems/cc9ca7da-0676-4229-aeca-d47c10a14c25
-- title:
--   (5.21)–(5.23) — e^{λt}φ(x) solves the delayed damped wave equation when φ is a Λ² eigenfunction and λ solves (5.23)
-- statement:
--   Let $(\Omega, \Gamma_D, \Gamma_N)$ be a mixed domain, $\mu_1, \mu_2, \tau, \Lambda \in \mathbb R$. Let $\varphi : \mathbb R^n \to \mathbb C$ be $C^2$ on $\Omega$ and $C^1$ on $\overline\Omega$, and an eigenfunction of the mixed Dirichlet–Neumann Laplacian with eigenvalue $\Lambda^2$:
--   $$\Delta\varphi = -\Lambda^2\varphi \ \text{ in } \Omega, \qquad \varphi = 0 \ \text{ on } \Gamma_D, \qquad \frac{\partial\varphi}{\partial\nu} = 0 \ \text{ on } \Gamma_N .$$
--   If $\lambda \in \mathbb C$ solves the characteristic equation
--   $$\lambda^2 + \big(\mu_1 + \mu_2 e^{-\lambda\tau}\big)\lambda = -\Lambda^2, \tag{5.23}$$
--   then $u(x,t) = e^{\lambda t}\varphi(x)$ is a classical solution of
--   $$u_{tt} - \Delta u + \mu_1 u_t(x,t) + \mu_2 u_t(x,t-\tau) = 0 \ \text{ in } \Omega\times(0,\infty), \quad u = 0 \ \text{ on } \Gamma_D, \quad \frac{\partial u}{\partial\nu} = 0 \ \text{ on } \Gamma_N,$$
--   i.e. of problem (1.12)–(1.14) with $a \equiv 1$.
--
--   This is the separation-of-variables step of §5.2: it reduces the construction of non-decaying solutions to finding a root $\lambda$ of the scalar transcendental equation (5.23) for an eigenvalue $\Lambda^2$ of (5.22).
--
--   **Formalization Note** The paper's (5.22) prints $\Delta\varphi = -\mu^2\varphi$; the following sentence ("for any $\Lambda^2$ eigenvalue of problem (5.22)") shows that $-\Lambda^2\varphi$ is meant, which is what is stated. The positivity assumptions $\mu_1, \mu_2, \tau > 0$ of the paper are not needed for this step and are omitted, which makes the statement more general.
-- source:
--   Nicaise, Pignotti, Stability and Instability Results of the Wave Equation with a Delay Term in the Boundary or Internal Feedbacks, SIAM J. Control Optim. 45 (2006), p. 1583, §5.2, (5.20)–(5.23)

import Mathlib
import Definitions.Def_NicaiseDelayWave_InternalInstab_DelayProblem

namespace NicaiseDelayWave.InternalInstab

/-- Nicaise–Pignotti, §5.2, p. 1583, (5.21)–(5.23): if `φ` is an eigenfunction of the mixed
Dirichlet–Neumann Laplacian (5.22) with eigenvalue `Λ²` and `λ ∈ ℂ` solves the characteristic
equation (5.23), then `u(x, t) = e^{λt} φ(x)` solves (5.20) (problem (1.12)–(1.14) with `a ≡ 1`). -/
theorem eq5_21_separated_solution {n : ℕ} (D : NicaiseDelayWave.Shared.MixedDomain n) (μ₁ μ₂ τ Λ : ℝ)
    (φ : EuclideanSpace ℝ (Fin n) → ℂ)
    (hφ₂ : ContDiffOn ℝ 2 φ D.Ω) (hφ₁ : ContDiffOn ℝ 1 φ (closure D.Ω))
    (hΔ : ∀ x ∈ D.Ω, laplacian φ x = -((Λ : ℂ) ^ 2) * φ x)
    (hD : ∀ x ∈ D.ΓD, φ x = 0)
    (hN : ∀ x ∈ D.ΓN, normalDeriv D φ x = 0)
    (lam : ℂ)
    (hlam : lam ^ 2 + ((μ₁ : ℂ) + (μ₂ : ℂ) * Complex.exp (-lam * τ)) * lam = -((Λ : ℂ) ^ 2)) :
    IsClassicalSolution D μ₁ μ₂ τ (fun x t => Complex.exp (lam * t) * φ x) := by sorry

end NicaiseDelayWave.InternalInstab

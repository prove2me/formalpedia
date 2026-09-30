-- Prove2me | Theorems.Thm_NicaiseDelayWave_BoundaryInstab_eq5_1_5_2_separated_solution
-- name    : NicaiseDelayWave.BoundaryInstab.eq5_1_5_2_separated_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T20:45:43.570217+00:00
-- url     : https://prove2.me/theorems/94103f38-c6f2-4d76-89df-22456af070b3
-- title:
--   (5.1)–(5.2) — a solution φ of the eigenvalue problem gives the solution u = e^{λt}φ of the delayed problem
-- statement:
--   Let $(\Omega, \Gamma_D, \Gamma_N)$ be a mixed domain with outer unit normal $\nu$, let $\mu_1, \mu_2 > 0$ and $\tau > 0$, and let $\lambda \in \mathbb C$. Let $\varphi : \mathbb R^n \to \mathbb C$ be $C^2$ in $\Omega$ and $C^1$ on $\overline\Omega$, and suppose that $\varphi$ solves the eigenvalue problem (5.2):
--   $$\begin{cases} -\Delta\varphi + \lambda^2\varphi = 0 & \text{in } \Omega,\\ \varphi = 0 & \text{on } \Gamma_D,\\ \dfrac{\partial\varphi}{\partial\nu} = -(\mu_1 + \mu_2 e^{-\lambda\tau})\lambda\varphi & \text{on } \Gamma_N. \end{cases}$$
--   Then the separated function
--   $$u(x,t) = e^{\lambda t}\varphi(x)$$
--   is a classical solution of the wave equation with delayed boundary feedback (5.1) = (1.1)–(1.3) with delay $\tau$.
--
--   This is the reduction of §5.1: every solution of the spectral problem (5.2) yields an explicit solution of the evolution problem, and the rest of the section only has to produce $\lambda = ib$ and $\varphi$.
--
--   **Formalization Note** The solution is complex-valued and defined for all $t \in \mathbb R$; its values at $t \le 0$ are the initial data and the history. The normal derivative is taken within $\overline\Omega$.
-- source:
--   Nicaise, Pignotti, Stability and Instability Results of the Wave Equation with a Delay Term in the Boundary or Internal Feedbacks, SIAM J. Control Optim. 45 (2006), pp. 1579–1580, §5.1, (5.1)–(5.2)

import Mathlib
import Definitions.Def_NicaiseDelayWave_Shared_MixedDomain
import Definitions.Def_NicaiseDelayWave_BoundaryInstab_DelayProblem

open MeasureTheory

namespace NicaiseDelayWave.BoundaryInstab

/-- (5.1)–(5.2): if `λ ∈ ℂ` and `φ` (`C²` in `Ω`, `C¹` up to the boundary) solves the eigenvalue
problem `-Δφ + λ²φ = 0` in `Ω`, `φ = 0` on `Γ_D`, `∂φ/∂ν = -(μ₁ + μ₂ e^{-λτ}) λ φ` on `Γ_N`,
then `u(x, t) = e^{λt} φ(x)` is a classical solution of (5.1). -/
theorem eq5_1_5_2_separated_solution {n : ℕ} (D : NicaiseDelayWave.Shared.MixedDomain n) (μ1 μ2 τ : ℝ)
    (hμ1 : 0 < μ1) (hμ2 : 0 < μ2) (hτ : 0 < τ) (lam : ℂ)
    (φ : EuclideanSpace ℝ (Fin n) → ℂ)
    (hφ2 : ContDiffOn ℝ 2 φ D.Ω) (hφ1 : ContDiffOn ℝ 1 φ (closure D.Ω))
    (heq : ∀ x ∈ D.Ω, -laplacian φ x + lam ^ 2 * φ x = 0)
    (hD : ∀ x ∈ D.ΓD, φ x = 0)
    (hN : ∀ x ∈ D.ΓN,
      normalDeriv D φ x = -((μ1 : ℂ) + (μ2 : ℂ) * Complex.exp (-lam * τ)) * lam * φ x) :
    IsClassicalSolution D μ1 μ2 τ (fun x t => Complex.exp (lam * t) * φ x) := by sorry

end NicaiseDelayWave.BoundaryInstab

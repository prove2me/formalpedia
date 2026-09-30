-- Prove2me | Theorems.Thm_NicaiseDelayWave_BoundaryInstab_case_a_constant_energy
-- name    : NicaiseDelayWave.BoundaryInstab.case_a_constant_energy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T20:59:42.46486+00:00
-- url     : https://prove2.me/theorems/4308f96b-c342-47c6-806f-803e9362079d
-- title:
--   Case (a), μ1 = μ2 — a Dirichlet–Neumann eigenfunction φ gives u = e^{ibt}φ with ∫_Ω(|∇u|² + |u_t|²)dx = 2b² for τ = (2l+1)π/b
-- statement:
--   Let $(\Omega, \Gamma_D, \Gamma_N)$ be a mixed domain, let $\mu_1 = \mu_2 = \mu > 0$, $b > 0$, $l \in \mathbb N$, and
--   $$\tau = \frac{(2l+1)\pi}{b}.$$
--   Let $\varphi : \mathbb R^n \to \mathbb R$ be $C^2$ in $\Omega$ and $C^1$ on $\overline\Omega$, an eigenfunction of the Laplacian with mixed Dirichlet–Neumann boundary conditions,
--   $$-\Delta\varphi = b^2\varphi \ \text{ in } \Omega, \qquad \varphi = 0 \ \text{ on } \Gamma_D, \qquad \frac{\partial\varphi}{\partial\nu} = 0 \ \text{ on } \Gamma_N,$$
--   normalised by $\int_\Omega \varphi^2\,dx = 1$. Then
--   $$u(x,t) = e^{ibt}\varphi(x)$$
--   is a classical solution of (1.1)–(1.3) with $\mu_1 = \mu_2 = \mu$ and delay $\tau$, and for every $t \ge 0$
--   $$\int_\Omega \big(|\nabla u(x,t)|^2 + |u_t(x,t)|^2\big)\,dx = 2\mathcal E(t) = 2b^2 .$$
--
--   This is case (a) of §5.1: when $\mu_1 = \mu_2$, the delays $\tau_{n,l} = (2l+1)\pi/b_n$ built from the eigenvalues $b_n^2$ carry solutions whose standard energy never decays, so the problem is not asymptotically stable.
--
--   **Formalization Note** The paper obtains $\varphi$ as a minimiser of $q_1$ on the unit sphere of $H^1_{\Gamma_D}(\Omega)$ (5.13) and then notes that (5.2) becomes the classical mixed Dirichlet–Neumann eigenvalue problem; the statement takes $\varphi$ as such an eigenfunction, in the classical class ($C^2$ inside, $C^1$ up to the boundary). The normal derivative is taken within $\overline\Omega$. The identity is stated as $2\mathcal E(t) = 2b^2$, where $\mathcal E$ is the standard energy (3.7) with $|u_t|^2$, $|\nabla u|^2$ the squared moduli.
-- source:
--   Nicaise, Pignotti, Stability and Instability Results of the Wave Equation with a Delay Term in the Boundary or Internal Feedbacks, SIAM J. Control Optim. 45 (2006), p. 1581, §5.1, Case (a), (5.13)–(5.14) and the following paragraph

import Mathlib
import Definitions.Def_NicaiseDelayWave_Shared_MixedDomain
import Definitions.Def_NicaiseDelayWave_BoundaryInstab_DelayProblem

open MeasureTheory

namespace NicaiseDelayWave.BoundaryInstab

/-- Case (a), `μ₁ = μ₂` (p. 1581, (5.13)–(5.14)): let `φ` be a real eigenfunction of the Laplacian
with mixed Dirichlet–Neumann conditions, `-Δφ = b²φ` in `Ω`, `φ = 0` on `Γ_D`, `∂φ/∂ν = 0` on
`Γ_N`, normalised by `∫_Ω φ² = 1`, with `b > 0`, and let `τ = (2l+1)π/b`. Then
`u(x,t) = e^{ibt} φ(x)` is a classical solution of (1.1)–(1.3) with `μ₁ = μ₂ = μ` and delay `τ`,
and `∫_Ω (|∇u|² + |u_t|²) dx = 2𝓔(t) = 2b²` for all `t ≥ 0`. -/
theorem case_a_constant_energy {n : ℕ} (D : NicaiseDelayWave.Shared.MixedDomain n) (μ b : ℝ) (hμ : 0 < μ)
    (hb : 0 < b) (l : ℕ) (τ : ℝ) (hτ : τ = (2 * l + 1) * Real.pi / b)
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) (hφ : φ ∈ admissible D)
    (heig : ∀ x ∈ D.Ω, -laplacian φ x = b ^ 2 * φ x)
    (hN : ∀ x ∈ D.ΓN, normalDeriv D φ x = 0)
    (hnorm : ∫ x in D.Ω, φ x ^ 2 = 1) :
    IsClassicalSolution D μ μ τ (fun x t => Complex.exp (Complex.I * b * t) * (φ x : ℂ)) ∧
      ∀ t ≥ 0,
        2 * stdEnergy D (fun x t => Complex.exp (Complex.I * b * t) * (φ x : ℂ)) t =
          2 * b ^ 2 := by sorry

end NicaiseDelayWave.BoundaryInstab

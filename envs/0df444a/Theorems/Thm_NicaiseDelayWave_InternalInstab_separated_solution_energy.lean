-- Prove2me | Theorems.Thm_NicaiseDelayWave_InternalInstab_separated_solution_energy
-- name    : NicaiseDelayWave.InternalInstab.separated_solution_energy
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T22:20:55.174078+00:00
-- url     : https://prove2.me/theorems/be4a7e14-6730-4a2c-a54a-60fbe0e5551b
-- title:
--   §5.2, p. 1584 — the standard energy of e^{λt}φ(x) is e^{2 Re(λ) t} times a positive constant
-- statement:
--   Let $(\Omega, \Gamma_D, \Gamma_N)$ be a mixed domain, let $\varphi : \mathbb R^n \to \mathbb C$ be $C^1$ on $\overline\Omega$ and not identically zero on $\Omega$, and let $\lambda \in \mathbb C$, $\lambda \neq 0$. Let $\mathcal E(t)$ be the standard energy of $u(x,t) = e^{\lambda t}\varphi(x)$,
--   $$\mathcal E(t) = \frac12\int_\Omega \Big\{ |u_t(x,t)|^2 + |\nabla u(x,t)|^2 \Big\}\,dx .$$
--   Then $\mathcal E(0) > 0$ and
--   $$\mathcal E(t) = e^{2\,\mathrm{Re}(\lambda)\, t}\,\mathcal E(0) \qquad \text{for all } t \in \mathbb R .$$
--
--   In particular the energy is constant and strictly positive when $\mathrm{Re}\,\lambda = 0$ (Case (a) of §5.2), and it does not tend to $0$ when $\mathrm{Re}\,\lambda \ge 0$ (Case (b)). This is the last step of the instability argument.
--
--   **Formalization Note** The paper's "$e^{\alpha+i\beta}\varphi(x)$" (p. 1584) is a misprint for $e^{(\alpha+i\beta)t}\varphi(x)$. The identity holds for every $\lambda$; the hypothesis $\lambda \neq 0$ is only needed for $\mathcal E(0) > 0$ (for $\lambda = 0$ a nonzero constant $\varphi$ has zero energy).
-- source:
--   Nicaise, Pignotti, Stability and Instability Results of the Wave Equation with a Delay Term in the Boundary or Internal Feedbacks, SIAM J. Control Optim. 45 (2006), p. 1584, §5.2 ("whose energy is constant and strictly positive"; "Since α ≥ 0, the energy of such a solution is not decaying to zero")

import Mathlib
import Definitions.Def_NicaiseDelayWave_InternalInstab_DelayProblem

namespace NicaiseDelayWave.InternalInstab

/-- Nicaise–Pignotti, §5.2, p. 1584: the standard energy of a separated solution
`u(x, t) = e^{λt} φ(x)` equals `e^{2 Re(λ) t}` times its (strictly positive) value at `t = 0`;
in particular it is constant when `Re λ = 0` (Case (a)) and does not decay when `Re λ ≥ 0`. -/
theorem separated_solution_energy {n : ℕ} (D : NicaiseDelayWave.Shared.MixedDomain n)
    (φ : EuclideanSpace ℝ (Fin n) → ℂ) (hφ₁ : ContDiffOn ℝ 1 φ (closure D.Ω))
    (hφ_ne : ∃ x ∈ D.Ω, φ x ≠ 0) (lam : ℂ) (hlam : lam ≠ 0) :
    0 < stdEnergy D (fun x t => Complex.exp (lam * t) * φ x) 0 ∧
      ∀ t : ℝ, stdEnergy D (fun x t => Complex.exp (lam * t) * φ x) t
        = Real.exp (2 * lam.re * t) * stdEnergy D (fun x t => Complex.exp (lam * t) * φ x) 0 := by sorry

end NicaiseDelayWave.InternalInstab

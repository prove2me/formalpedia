-- Prove2me | Theorems.Thm_NicaiseDelayWave_BoundaryStab_theorem1_1_exponential_stability
-- name    : NicaiseDelayWave.BoundaryStab.theorem1_1_exponential_stability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T18:00:10.681316+00:00
-- url     : https://prove2.me/theorems/5120f402-54b4-4d3a-8a20-641f16ffccc6
-- title:
--   Theorem 1.1 — exponential decay E(t) ≤ C₁E(0)e^{−C₂t} under delayed boundary feedback when μ₂ < μ₁
-- statement:
--   Let $\Omega \subset \mathbb R^n$, $n \ge 1$, be a bounded open set, each of whose connected components has a boundary point in $\Gamma_D$, with $C^2$ boundary $\Gamma = \Gamma_D \cup \Gamma_N$, $\overline{\Gamma_D}\cap\overline{\Gamma_N} = \emptyset$, $\Gamma_D \ne \emptyset$, outer unit normal $\nu$ and surface measure $d\Gamma$. Suppose there are a $C^2$ function $v$ and $\alpha > 0$ with
--   $$\langle D^2v(x)\xi,\xi\rangle \ge 2\alpha|\xi|^2 \quad (x \in \overline\Omega,\ \xi\in\mathbb R^n), \qquad \nabla v(x)\cdot\nu(x) \le 0 \quad (x \in \Gamma_D). \tag{1.6–1.7}$$
--   Let $\mu_1, \mu_2, \tau > 0$ with $\mu_2 < \mu_1$ (1.8), and let $\xi$ satisfy $\tau\mu_2 < \xi < \tau(2\mu_1-\mu_2)$ (1.10).
--
--   Then there are constants $C_1, C_2 > 0$ such that every regular solution $u$ of
--   $$u_{tt} - \Delta u = 0 \text{ in } \Omega\times(0,\infty),\qquad u = 0 \text{ on } \Gamma_D\times(0,\infty),\qquad \frac{\partial u}{\partial\nu}(x,t) = -\mu_1u_t(x,t) - \mu_2u_t(x,t-\tau) \text{ on } \Gamma_N\times(0,\infty)$$
--   satisfies
--   $$E(t) \le C_1E(0)e^{-C_2t} \qquad \forall t \ge 0, \tag{1.11}$$
--   where
--   $$E(t) = \frac12\int_\Omega\{u_t^2(x,t)+|\nabla u(x,t)|^2\}\,dx + \frac\xi2\int_{\Gamma_N}\int_0^1u_t^2(x,t-\tau\rho)\,d\rho\,d\Gamma. \tag{1.9}$$
--
--   The theorem shows that a delayed boundary velocity feedback does not destroy the exponential stabilization produced by an undelayed one, provided the delayed gain $\mu_2$ is smaller than the undelayed gain $\mu_1$. The paper's Theorem 1.2 shows that the condition cannot be dropped.
--
--   **Formalization Note** $C_1, C_2$ depend only on the data (domain, $v$, $\alpha$, $\mu_1,\mu_2,\tau,\xi$), not on $u$. Solutions are classical: $u$ is one $C^2$ function on $\mathbb R^n\times\mathbb R$, with the equations imposed for $t > 0$ and the initial data and history read off at $t \le 0$; the paper's theorem also covers the weaker solutions of its well-posedness Theorem 2.1, so this is the paper's theorem restricted to classical solutions. The hypothesis that every connected component of $\Omega$ has a boundary point in $\Gamma_D$ is added (it holds whenever $\Omega$ is connected): the paper assumes only an open bounded set, and its compactness–uniqueness step needs every component of $\Omega$ to meet $\Gamma_D$.
-- source:
--   Nicaise, Pignotti, Stability and Instability Results of the Wave Equation with a Delay Term in the Boundary or Internal Feedbacks, SIAM J. Control Optim. 45 (2006), p. 1563, Theorem 1.1, eq. (1.11); setting p. 1561–1562

import Mathlib
import Definitions.Def_NicaiseDelayWave_Shared_MixedDomain
import Definitions.Def_NicaiseDelayWave_BoundaryStab_DelayProblem
import Definitions.Def_NicaiseDelayWave_BoundaryStab_ConvexMultiplier

open MeasureTheory

namespace NicaiseDelayWave.BoundaryStab

theorem theorem1_1_exponential_stability {n : ℕ} (hn : 1 ≤ n) (D : NicaiseDelayWave.Shared.MixedDomain n)
    (hcomp : ∀ x ∈ D.Ω, (closure (connectedComponentIn D.Ω x) ∩ D.ΓD).Nonempty)
    (v : EuclideanSpace ℝ (Fin n) → ℝ) (α : ℝ)
    (hv : ConvexMultiplier D v α) (μ1 μ2 τ ξ : ℝ) (hμ1 : 0 < μ1) (hμ2 : 0 < μ2) (hτ : 0 < τ)
    (h18 : μ2 < μ1) (h110 : τ * μ2 < ξ ∧ ξ < τ * (2 * μ1 - μ2)) :
    ∃ C1 C2 : ℝ, 0 < C1 ∧ 0 < C2 ∧
      ∀ u : EuclideanSpace ℝ (Fin n) → ℝ → ℝ, IsRegularSolution D μ1 μ2 τ u →
        ∀ t : ℝ, 0 ≤ t → energy D ξ τ u t ≤ C1 * energy D ξ τ u 0 * Real.exp (-C2 * t) := by sorry

end NicaiseDelayWave.BoundaryStab

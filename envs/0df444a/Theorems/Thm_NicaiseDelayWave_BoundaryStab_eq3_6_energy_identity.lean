-- Prove2me | Theorems.Thm_NicaiseDelayWave_BoundaryStab_eq3_6_energy_identity
-- name    : NicaiseDelayWave.BoundaryStab.eq3_6_energy_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T17:35:19.319513+00:00
-- url     : https://prove2.me/theorems/54e97317-8dc4-4bdd-a418-fa28e75ca293
-- title:
--   (3.6) — the energy identity for E′(t)
-- statement:
--   Let $(\Omega, \Gamma_D, \Gamma_N)$ be a mixed domain in $\mathbb R^n$, $n \ge 1$, with surface measure $d\Gamma$, and let $\mu_1, \mu_2, \tau, \xi > 0$. Let $u$ be a regular solution of the wave equation with delayed boundary feedback (1.1)–(1.3), and let $E$ be its energy (1.9). Then for every $t > 0$ the energy is differentiable at $t$ and
--   $$E'(t) = -\mu_1\int_{\Gamma_N} u_t^2(x,t)\,d\Gamma - \mu_2\int_{\Gamma_N} u_t(x,t)\,u_t(x,t-\tau)\,d\Gamma + \frac{\xi\tau^{-1}}{2}\int_{\Gamma_N} u_t^2(x,t)\,d\Gamma - \frac{\xi\tau^{-1}}{2}\int_{\Gamma_N} u_t^2(x,t-\tau)\,d\Gamma.$$
--
--   The identity expresses all energy exchange through the feedback boundary $\Gamma_N$; it is the starting point of the dissipation estimate (Proposition 3.1).
--
--   **Formalization Note** Differentiability is asserted (`HasDerivAt`), not presupposed. The identity needs neither the geometric hypothesis (1.6)–(1.7) nor the conditions (1.8), (1.10); those are omitted, which makes the statement stronger than the section's standing setting requires.
-- source:
--   Nicaise, Pignotti, Stability and Instability Results of the Wave Equation with a Delay Term in the Boundary or Internal Feedbacks, SIAM J. Control Optim. 45 (2006), p. 1570, §3, eq. (3.6) (proof of Proposition 3.1)

import Mathlib
import Definitions.Def_NicaiseDelayWave_Shared_MixedDomain
import Definitions.Def_NicaiseDelayWave_BoundaryStab_DelayProblem

open MeasureTheory

namespace NicaiseDelayWave.BoundaryStab

theorem eq3_6_energy_identity {n : ℕ} (hn : 1 ≤ n) (D : NicaiseDelayWave.Shared.MixedDomain n)
    (μ1 μ2 τ ξ : ℝ) (hμ1 : 0 < μ1) (hμ2 : 0 < μ2) (hτ : 0 < τ) (hξ : 0 < ξ)
    (u : EuclideanSpace ℝ (Fin n) → ℝ → ℝ) (hu : IsRegularSolution D μ1 μ2 τ u)
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s => energy D ξ τ u s)
      (-μ1 * ∫ x in D.ΓN, ut u x t ^ 2 ∂D.σ
        - μ2 * ∫ x in D.ΓN, ut u x t * ut u x (t - τ) ∂D.σ
        + ξ / (2 * τ) * ∫ x in D.ΓN, ut u x t ^ 2 ∂D.σ
        - ξ / (2 * τ) * ∫ x in D.ΓN, ut u x (t - τ) ^ 2 ∂D.σ) t := by sorry

end NicaiseDelayWave.BoundaryStab

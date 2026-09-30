-- Prove2me | Theorems.Thm_NicaiseDelayWave_BoundaryStab_eq3_22_integrated_dissipation
-- name    : NicaiseDelayWave.BoundaryStab.eq3_22_integrated_dissipation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T17:45:19.901989+00:00
-- url     : https://prove2.me/theorems/659c6917-2640-4662-9db9-6f4e5928d117
-- title:
--   (3.22) — E(T) − E(0) ≤ −C∫_0^T∫_{Γ_N}{u_t²(t) + u_t²(t − τ)}dΓdt
-- statement:
--   Under the hypotheses of Proposition 3.1 — a mixed domain in $\mathbb R^n$, $n\ge1$, $\mu_1, \mu_2, \tau > 0$, $\mu_2 < \mu_1$ (1.8) and $\tau\mu_2 < \xi < \tau(2\mu_1 - \mu_2)$ (1.10) — let
--   $$C = \min\Big\{\mu_1 - \frac{\mu_2}{2} - \frac{\xi\tau^{-1}}{2},\ -\frac{\mu_2}{2} + \frac{\xi\tau^{-1}}{2}\Big\}.$$
--   For every regular solution $u$ of (1.1)–(1.3) with energy $E$ (1.9) and every $T \ge 0$,
--   $$E(T) - E(0) \le -C\int_0^T\int_{\Gamma_N}\{u_t^2(x,t) + u_t^2(x,t-\tau)\}\,d\Gamma\,dt. \tag{3.22}$$
--
--   This is the integrated form of the dissipation inequality (3.1); combined with the observability inequality (3.10) it gives the contraction $E(T) \le \tilde C E(0)$, $\tilde C < 1$.
--
--   **Formalization Note** The constant $C$ is the explicit one of Proposition 3.1. The geometric hypothesis (1.6)–(1.7) is not needed and is omitted.
-- source:
--   Nicaise, Pignotti, Stability and Instability Results of the Wave Equation with a Delay Term in the Boundary or Internal Feedbacks, SIAM J. Control Optim. 45 (2006), p. 1573, §3, eq. (3.22) (proof of Theorem 1.1)

import Mathlib
import Definitions.Def_NicaiseDelayWave_Shared_MixedDomain
import Definitions.Def_NicaiseDelayWave_BoundaryStab_DelayProblem

open MeasureTheory

namespace NicaiseDelayWave.BoundaryStab

theorem eq3_22_integrated_dissipation {n : ℕ} (hn : 1 ≤ n) (D : NicaiseDelayWave.Shared.MixedDomain n)
    (μ1 μ2 τ ξ : ℝ) (hμ1 : 0 < μ1) (hμ2 : 0 < μ2) (hτ : 0 < τ) (h18 : μ2 < μ1)
    (h110 : τ * μ2 < ξ ∧ ξ < τ * (2 * μ1 - μ2))
    (u : EuclideanSpace ℝ (Fin n) → ℝ → ℝ) (hu : IsRegularSolution D μ1 μ2 τ u)
    (T : ℝ) (hT : 0 ≤ T) :
    energy D ξ τ u T - energy D ξ τ u 0 ≤
      -(min (μ1 - μ2 / 2 - ξ / (2 * τ)) (-μ2 / 2 + ξ / (2 * τ)))
        * ∫ t in (0 : ℝ)..T, boundaryDissipation D τ u t := by sorry

end NicaiseDelayWave.BoundaryStab

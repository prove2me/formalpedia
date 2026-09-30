-- Prove2me | Theorems.Thm_NicaiseDelayWave_BoundaryStab_proposition3_1_energy_decreasing
-- name    : NicaiseDelayWave.BoundaryStab.proposition3_1_energy_decreasing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T17:40:33.544981+00:00
-- url     : https://prove2.me/theorems/c233e3e1-9641-49f3-a67c-51a9425f6205
-- title:
--   Proposition 3.1 — E is nonincreasing and E′(t) ≤ −C∫_{Γ_N}{u_t²(t) + u_t²(t − τ)}dΓ
-- statement:
--   Let $(\Omega, \Gamma_D, \Gamma_N)$ be a mixed domain in $\mathbb R^n$, $n \ge 1$, and let $\mu_1, \mu_2, \tau > 0$ with
--   $$\mu_2 < \mu_1 \tag{1.8}$$
--   and let $\xi$ satisfy
--   $$\tau\mu_2 < \xi < \tau(2\mu_1 - \mu_2). \tag{1.10}$$
--   Put
--   $$C = \min\Big\{\mu_1 - \frac{\mu_2}{2} - \frac{\xi\tau^{-1}}{2},\ -\frac{\mu_2}{2} + \frac{\xi\tau^{-1}}{2}\Big\}.$$
--   Then $C > 0$, and for every regular solution $u$ of (1.1)–(1.3) with energy $E$ (1.9):
--
--   1. $E$ is nonincreasing on $[0, \infty)$;
--   2. for every $t > 0$, $E$ is differentiable at $t$ and
--   $$E'(t) \le -C\int_{\Gamma_N}\{u_t^2(x,t) + u_t^2(x,t-\tau)\}\,d\Gamma. \tag{3.1}$$
--
--   This dissipation inequality is one of the two ingredients of the exponential decay theorem: it shows that the energy loss on $[0,T]$ controls the boundary observation $\int_0^T\int_{\Gamma_N}\{u_t^2(t) + u_t^2(t-\tau)\}$.
--
--   **Formalization Note** The paper's "there exists a positive constant $C$" is stated with the explicit constant computed at the end of its proof, which is stronger. "Decreasing" is read as nonincreasing (the zero solution has constant energy). The geometric hypothesis (1.6)–(1.7) is not needed and is omitted.
-- source:
--   Nicaise, Pignotti, Stability and Instability Results of the Wave Equation with a Delay Term in the Boundary or Internal Feedbacks, SIAM J. Control Optim. 45 (2006), p. 1569, Proposition 3.1, eq. (3.1); constant C on p. 1570

import Mathlib
import Definitions.Def_NicaiseDelayWave_Shared_MixedDomain
import Definitions.Def_NicaiseDelayWave_BoundaryStab_DelayProblem

open MeasureTheory

namespace NicaiseDelayWave.BoundaryStab

theorem proposition3_1_energy_decreasing {n : ℕ} (hn : 1 ≤ n) (D : NicaiseDelayWave.Shared.MixedDomain n)
    (μ1 μ2 τ ξ : ℝ) (hμ1 : 0 < μ1) (hμ2 : 0 < μ2) (hτ : 0 < τ) (h18 : μ2 < μ1)
    (h110 : τ * μ2 < ξ ∧ ξ < τ * (2 * μ1 - μ2)) :
    0 < min (μ1 - μ2 / 2 - ξ / (2 * τ)) (-μ2 / 2 + ξ / (2 * τ)) ∧
    ∀ u : EuclideanSpace ℝ (Fin n) → ℝ → ℝ, IsRegularSolution D μ1 μ2 τ u →
      AntitoneOn (fun s => energy D ξ τ u s) (Set.Ici 0) ∧
      ∀ t : ℝ, 0 < t → ∃ E' : ℝ, HasDerivAt (fun s => energy D ξ τ u s) E' t ∧
        E' ≤ -(min (μ1 - μ2 / 2 - ξ / (2 * τ)) (-μ2 / 2 + ξ / (2 * τ)))
          * boundaryDissipation D τ u t := by sorry

end NicaiseDelayWave.BoundaryStab

-- Prove2me | Theorems.Thm_NicaiseDelayWave_BoundaryStab_proposition3_2_observability
-- name    : NicaiseDelayWave.BoundaryStab.proposition3_2_observability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T17:50:07.989983+00:00
-- url     : https://prove2.me/theorems/c3b57e96-595b-4a5d-b994-be4d5567fef3
-- title:
--   Proposition 3.2 — boundary observability E(0) ≤ C₀∫_0^T∫_{Γ_N}{u_t²(t) + u_t²(t − τ)}dΓdt
-- statement:
--   Let $(\Omega, \Gamma_D, \Gamma_N)$ be a mixed domain in $\mathbb R^n$, $n \ge 1$, such that every connected component of $\Omega$ has a boundary point in $\Gamma_D$, and suppose there are a $C^2$ function $v$ and $\alpha > 0$ satisfying the geometric hypothesis (1.6)–(1.7). Let $\mu_1, \mu_2, \tau > 0$ with $\mu_2 < \mu_1$ (1.8) and let $\tau\mu_2 < \xi < \tau(2\mu_1 - \mu_2)$ (1.10).
--
--   Then there is a time $\overline T > 0$ such that for every $T > \overline T$ there is a constant $C_0 > 0$ (depending on $T$ and on the data above) with
--   $$E(0) \le C_0\int_0^T\int_{\Gamma_N}\{u_t^2(x,t) + u_t^2(x,t-\tau)\}\,d\Gamma\,dt \tag{3.10}$$
--   for every regular solution $u$ of (1.1)–(1.3), where $E$ is the energy (1.9).
--
--   This boundary observability inequality says that the full energy (including the delay term) at time $0$ is controlled by what is observed on the feedback boundary $\Gamma_N$ over a sufficiently long time window. With the dissipation inequality it yields exponential stability.
--
--   **Formalization Note** $\overline T$ depends only on the data (domain, $v$, $\alpha$, $\mu_1, \mu_2, \tau, \xi$); $C_0$ depends on those and on $T$; neither depends on $u$. The hypothesis that every connected component of $\Omega$ has a boundary point in $\Gamma_D$ is added (it holds whenever $\Omega$ is connected): the paper assumes only an open bounded set, but its compactness–uniqueness step (p. 1573) concludes $w \equiv 0$ from $-\Delta w = 0$, $w = 0$ on $\Gamma_D$, $\partial w/\partial\nu = 0$ on $\Gamma_N$, which requires every component of $\Omega$ to meet $\Gamma_D$. Components whose boundary lies in $\Gamma_D$ alone are already excluded by (1.6)–(1.7).
-- source:
--   Nicaise, Pignotti, Stability and Instability Results of the Wave Equation with a Delay Term in the Boundary or Internal Feedbacks, SIAM J. Control Optim. 45 (2006), p. 1571, Proposition 3.2, eq. (3.10)

import Mathlib
import Definitions.Def_NicaiseDelayWave_Shared_MixedDomain
import Definitions.Def_NicaiseDelayWave_BoundaryStab_DelayProblem
import Definitions.Def_NicaiseDelayWave_BoundaryStab_ConvexMultiplier

open MeasureTheory

namespace NicaiseDelayWave.BoundaryStab

theorem proposition3_2_observability {n : ℕ} (hn : 1 ≤ n) (D : NicaiseDelayWave.Shared.MixedDomain n)
    (hcomp : ∀ x ∈ D.Ω, (closure (connectedComponentIn D.Ω x) ∩ D.ΓD).Nonempty)
    (v : EuclideanSpace ℝ (Fin n) → ℝ) (α : ℝ)
    (hv : ConvexMultiplier D v α) (μ1 μ2 τ ξ : ℝ) (hμ1 : 0 < μ1) (hμ2 : 0 < μ2) (hτ : 0 < τ)
    (h18 : μ2 < μ1) (h110 : τ * μ2 < ξ ∧ ξ < τ * (2 * μ1 - μ2)) :
    ∃ Tbar : ℝ, 0 < Tbar ∧ ∀ T : ℝ, Tbar < T → ∃ C0 : ℝ, 0 < C0 ∧
      ∀ u : EuclideanSpace ℝ (Fin n) → ℝ → ℝ, IsRegularSolution D μ1 μ2 τ u →
        energy D ξ τ u 0 ≤ C0 * ∫ t in (0 : ℝ)..T, boundaryDissipation D τ u t := by sorry

end NicaiseDelayWave.BoundaryStab

-- Prove2me | Theorems.Thm_NicaiseDelayWave_InternalStab_proposition4_1_energy_decreasing
-- name    : NicaiseDelayWave.InternalStab.proposition4_1_energy_decreasing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T20:08:29.934233+00:00
-- url     : https://prove2.me/theorems/2aa3c6f7-c385-453b-8135-14b22efd7a75
-- title:
--   Proposition 4.1 — 𝓕 is nonincreasing and 𝓕′(t) ≤ −C∫_Ω a{u_t²(t) + u_t²(t − τ)}dx
-- statement:
--   Let $(\Omega,\Gamma_D,\Gamma_N)$ be a mixed domain, $a\in L^\infty(\Omega)$ with $a\ge0$ a.e., and let $\mu_1,\mu_2,\tau>0$ with $\mu_2<\mu_1$ (1.8) and $\xi$ satisfying (1.10), $\tau\mu_2<\xi<\tau(2\mu_1-\mu_2)$. Then there is a constant $C>0$, depending only on $\mu_1,\mu_2,\tau,\xi$, such that for every regular solution $u$ of (1.12)–(1.14) the energy $\mathcal F$ of (1.19) is nonincreasing on $[0,\infty)$ and, for every $t>0$, $\mathcal F$ is differentiable at $t$ with
--   $$\mathcal{F}'(t)\le -C\int_\Omega a(x)\big\{u_t^2(x,t)+u_t^2(x,t-\tau)\big\}\,dx .$$
--
--   Together with the observability inequality of Proposition 4.3 this dissipation estimate gives exponential decay of $\mathcal F$.
--
--   **Formalization Note** The constant $C$ is chosen before the solution $u$ (it is uniform over solutions, as in the proof, where $C=\min\{\mu_1-\mu_2/2-\xi/(2\tau),\ \xi/(2\tau)-\mu_2/2\}$). "Decreasing" is read as nonincreasing (the zero solution has constant energy). The hypotheses (1.6)–(1.7), (1.18) and the component condition on $\Omega$ are not needed and are omitted.
-- source:
--   Nicaise, Pignotti, Stability and Instability Results of the Wave Equation with a Delay Term in the Boundary or Internal Feedbacks, SIAM J. Control Optim. 45 (2006), p. 1574, Proposition 4.1 (4.1); constant C as in p. 1570, proof of Proposition 3.1

import Mathlib
import Definitions.Def_NicaiseDelayWave_InternalStab_InternalDampingProblem

namespace NicaiseDelayWave.InternalStab

open MeasureTheory

theorem proposition4_1_energy_decreasing {n : ℕ} (hn : 1 ≤ n) (D : NicaiseDelayWave.Shared.MixedDomain n)
    (a : EuclideanSpace ℝ (Fin n) → ℝ) (ha : IsDampingCoefficient D a)
    (μ1 μ2 τ ξ : ℝ) (hμ1 : 0 < μ1) (hμ2 : 0 < μ2) (hτ : 0 < τ) (h18 : μ2 < μ1)
    (h110 : τ * μ2 < ξ ∧ ξ < τ * (2 * μ1 - μ2)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ u : EuclideanSpace ℝ (Fin n) → ℝ → ℝ, IsRegularSolution D a μ1 μ2 τ u →
        AntitoneOn (energyF D a ξ τ u) (Set.Ici 0) ∧
        ∀ t > 0, ∃ E' : ℝ, HasDerivAt (energyF D a ξ τ u) E' t ∧
          E' ≤ -C * internalDissipation D a τ u t := by sorry

end NicaiseDelayWave.InternalStab

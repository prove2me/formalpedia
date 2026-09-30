-- Prove2me | Theorems.Thm_NicaiseDelayWave_InternalStab_eq4_4_energy_identity
-- name    : NicaiseDelayWave.InternalStab.eq4_4_energy_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T20:01:43.525489+00:00
-- url     : https://prove2.me/theorems/a997efed-e606-4bc4-a923-1f9b43ec5237
-- title:
--   Eq. (4.4) — the energy identity for 𝓕′(t) under delayed internal damping
-- statement:
--   Let $(\Omega,\Gamma_D,\Gamma_N)$ be a mixed domain in $\mathbb{R}^n$, $a\in L^\infty(\Omega)$ with $a\ge0$ a.e., and $\mu_1,\mu_2,\tau,\xi>0$. Let $u$ be a regular solution of (1.12)–(1.14) and let $\mathcal F$ be its energy (1.19). Then for every $t>0$ the energy is differentiable at $t$ and
--   $$\mathcal{F}'(t)=-\mu_1\int_\Omega a(x)u_t^2(x,t)\,dx-\mu_2\int_\Omega a(x)u_t(x,t)u_t(x,t-\tau)\,dx+\frac{\xi\tau^{-1}}{2}\int_\Omega a(x)u_t^2(x,t)\,dx-\frac{\xi\tau^{-1}}{2}\int_\Omega a(x)u_t^2(x,t-\tau)\,dx .$$
--
--   This identity is the starting point of the dissipativity estimate (Proposition 4.1): the two delay-free terms come from the equation, the other two from differentiating the history term of $\mathcal F$.
--
--   **Formalization Note** The standing hypotheses (1.6)–(1.8), (1.10) and (1.18) are not used by this identity and are omitted, which makes the statement more general.
-- source:
--   Nicaise, Pignotti, Stability and Instability Results of the Wave Equation with a Delay Term in the Boundary or Internal Feedbacks, SIAM J. Control Optim. 45 (2006), p. 1575, §4, (4.4)

import Mathlib
import Definitions.Def_NicaiseDelayWave_InternalStab_InternalDampingProblem

namespace NicaiseDelayWave.InternalStab

open MeasureTheory

theorem eq4_4_energy_identity {n : ℕ} (hn : 1 ≤ n) (D : NicaiseDelayWave.Shared.MixedDomain n)
    (a : EuclideanSpace ℝ (Fin n) → ℝ) (ha : IsDampingCoefficient D a)
    (μ1 μ2 τ ξ : ℝ) (hμ1 : 0 < μ1) (hμ2 : 0 < μ2) (hτ : 0 < τ) (hξ : 0 < ξ)
    (u : EuclideanSpace ℝ (Fin n) → ℝ → ℝ) (hu : IsRegularSolution D a μ1 μ2 τ u)
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt (energyF D a ξ τ u)
      (-μ1 * (∫ x in D.Ω, a x * ut u x t ^ 2)
        - μ2 * (∫ x in D.Ω, a x * (ut u x t * ut u x (t - τ)))
        + ξ * τ⁻¹ / 2 * (∫ x in D.Ω, a x * ut u x t ^ 2)
        - ξ * τ⁻¹ / 2 * (∫ x in D.Ω, a x * ut u x (t - τ) ^ 2)) t := by sorry

end NicaiseDelayWave.InternalStab

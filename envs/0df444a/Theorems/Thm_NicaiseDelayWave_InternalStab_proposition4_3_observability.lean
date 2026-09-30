-- Prove2me | Theorems.Thm_NicaiseDelayWave_InternalStab_proposition4_3_observability
-- name    : NicaiseDelayWave.InternalStab.proposition4_3_observability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T20:19:56.205103+00:00
-- url     : https://prove2.me/theorems/090b124c-4abf-4d76-9f8a-f30438694b9f
-- title:
--   Proposition 4.3 — observability 𝓕(0) ≤ C0∫_0^T∫_Ω a{u_t²(t) + u_t²(t − τ)}dx dt
-- statement:
--   Assume the standing setting: $(\Omega,\Gamma_D,\Gamma_N)$ a mixed domain in $\mathbb{R}^n$ ($n\ge1$) such that the closure of every connected component of $\Omega$ meets $\Gamma_D$; $v,\alpha$ satisfying (1.6)–(1.7); $\omega\subset\Omega$ an open neighbourhood of $\Gamma_N$ in $\Omega$; $a\in L^\infty(\Omega)$ with $a\ge0$ a.e. in $\Omega$ (1.17) and $a>a_0>0$ a.e. in $\omega$ (1.18); $\mu_1,\mu_2,\tau>0$ with $\mu_2<\mu_1$ (1.8); $\xi$ satisfying (1.10). Then there is a time $\overline T$ such that for every $T>\overline T$ there is a constant $C_0>0$ (depending on $T$) for which
--   $$\mathcal{F}(0)\le C_0\int_0^T\int_\Omega a(x)\big\{u_t^2(x,t)+u_t^2(x,t-\tau)\big\}\,dx\,dt$$
--   for every regular solution $u$ of (1.12)–(1.14), where $\mathcal F$ is the energy (1.19).
--
--   Combined with the dissipation estimate of Proposition 4.1 it yields a contraction of the energy over one time interval of length $T$, hence exponential decay.
--
--   **Formalization Note** The condition that every connected component of $\Omega$ has a point of $\Gamma_D$ in its closure is added (see Proposition 4.2). $\overline T$ is existential, as printed.
-- source:
--   Nicaise, Pignotti, Stability and Instability Results of the Wave Equation with a Delay Term in the Boundary or Internal Feedbacks, SIAM J. Control Optim. 45 (2006), p. 1578, Proposition 4.3 (4.26)

import Mathlib
import Definitions.Def_NicaiseDelayWave_InternalStab_InternalDampingProblem

namespace NicaiseDelayWave.InternalStab

open MeasureTheory

theorem proposition4_3_observability {n : ℕ} (hn : 1 ≤ n) (D : NicaiseDelayWave.Shared.MixedDomain n)
    (hcomp : ∀ x ∈ D.Ω, (closure (connectedComponentIn D.Ω x) ∩ D.ΓD).Nonempty)
    (v : EuclideanSpace ℝ (Fin n) → ℝ) (α : ℝ) (hv : ConvexMultiplier D v α)
    (ω : Set (EuclideanSpace ℝ (Fin n))) (hω : IsInteriorNbhdΓN D ω)
    (a : EuclideanSpace ℝ (Fin n) → ℝ) (ha : IsDampingCoefficient D a)
    (a0 : ℝ) (ha0 : 0 < a0) (haω : ∀ᵐ x ∂(volume.restrict ω), a0 < a x)
    (μ1 μ2 τ ξ : ℝ) (hμ1 : 0 < μ1) (hμ2 : 0 < μ2) (hτ : 0 < τ) (h18 : μ2 < μ1)
    (h110 : τ * μ2 < ξ ∧ ξ < τ * (2 * μ1 - μ2)) :
    ∃ Tbar : ℝ, ∀ T > Tbar, ∃ C0 : ℝ, 0 < C0 ∧
      ∀ u : EuclideanSpace ℝ (Fin n) → ℝ → ℝ, IsRegularSolution D a μ1 μ2 τ u →
        energyF D a ξ τ u 0 ≤ C0 * ∫ t in (0 : ℝ)..T, internalDissipation D a τ u t := by sorry

end NicaiseDelayWave.InternalStab

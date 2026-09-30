-- Prove2me | Theorems.Thm_NicaiseDelayWave_InternalStab_proposition4_2_observability_free_wave
-- name    : NicaiseDelayWave.InternalStab.proposition4_2_observability_free_wave
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T20:14:33.072464+00:00
-- url     : https://prove2.me/theorems/33e1d471-57c5-45b2-9ae3-708d656eb794
-- title:
--   Proposition 4.2 — observability 𝓔_w(0) ≤ C1∫_0^T∫_ω w_t² dx dt for the undamped wave equation
-- statement:
--   Let $(\Omega,\Gamma_D,\Gamma_N)$ be a mixed domain in $\mathbb{R}^n$ ($n\ge1$) such that the closure of every connected component of $\Omega$ meets $\Gamma_D$, let $v,\alpha$ satisfy the convexity hypotheses (1.6)–(1.7), and let $\omega\subset\Omega$ be an open neighbourhood of $\Gamma_N$ in $\Omega$. Then there is a time $T_0$ such that for every $T>T_0$ there is a constant $C_1>0$ (depending on $T$) for which
--   $$\mathcal{E}_w(0)\le C_1\int_0^T\int_\omega w_t^2(x,t)\,dx\,dt$$
--   for every regular solution $w$ of the undamped mixed problem (4.7)–(4.9), where $\mathcal E_w(t)=\frac12\int_\Omega\{w_t^2+|\nabla w|^2\}dx$ is its standard energy (4.11).
--
--   This is the observability inequality for the conservative wave equation from a neighbourhood of the Neumann boundary; Proposition 4.3 transfers it to the damped delay system.
--
--   **Formalization Note** The hypothesis that the closure of every connected component of $\Omega$ meets $\Gamma_D$ is added (it holds whenever $\Omega$ is connected): the proof uses Poincaré's inequality on $\{w=0 \text{ on } \Gamma_D\}$, and its compactness–uniqueness step ends with a stationary solution that is harmonic, zero on $\Gamma_D$ and Neumann-zero on $\Gamma_N$, which vanishes only under this condition. $T_0$ is existential, as printed.
-- source:
--   Nicaise, Pignotti, Stability and Instability Results of the Wave Equation with a Delay Term in the Boundary or Internal Feedbacks, SIAM J. Control Optim. 45 (2006), p. 1576, Proposition 4.2 (4.12)

import Mathlib
import Definitions.Def_NicaiseDelayWave_InternalStab_InternalDampingProblem

namespace NicaiseDelayWave.InternalStab

open MeasureTheory

theorem proposition4_2_observability_free_wave {n : ℕ} (hn : 1 ≤ n) (D : NicaiseDelayWave.Shared.MixedDomain n)
    (hcomp : ∀ x ∈ D.Ω, (closure (connectedComponentIn D.Ω x) ∩ D.ΓD).Nonempty)
    (v : EuclideanSpace ℝ (Fin n) → ℝ) (α : ℝ) (hv : ConvexMultiplier D v α)
    (ω : Set (EuclideanSpace ℝ (Fin n))) (hω : IsInteriorNbhdΓN D ω) :
    ∃ T0 : ℝ, ∀ T > T0, ∃ C1 : ℝ, 0 < C1 ∧
      ∀ w : EuclideanSpace ℝ (Fin n) → ℝ → ℝ, IsFreeSolution D w →
        stdEnergy D w 0 ≤ C1 * ∫ t in (0 : ℝ)..T, ∫ x in ω, ut w x t ^ 2 := by sorry

end NicaiseDelayWave.InternalStab

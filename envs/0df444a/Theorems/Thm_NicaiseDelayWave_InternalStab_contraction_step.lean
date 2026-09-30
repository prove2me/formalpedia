-- Prove2me | Theorems.Thm_NicaiseDelayWave_InternalStab_contraction_step
-- name    : NicaiseDelayWave.InternalStab.contraction_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T20:26:56.92324+00:00
-- url     : https://prove2.me/theorems/98c2cfe2-b9be-4e76-a43e-49f60b06bcf0
-- title:
--   Contraction step — 𝓕(T) ≤ C̃𝓕(0) with C̃ < 1 (§4, p. 1579)
-- statement:
--   Under the standing setting of Theorem 1.3 (mixed domain in which every connected component of $\Omega$ has a point of $\Gamma_D$ in its closure, (1.6)–(1.7), $\omega$ an open neighbourhood of $\Gamma_N$ in $\Omega$, (1.17)–(1.18), $\mu_1,\mu_2,\tau>0$, (1.8) and (1.10)) there exist a time $T>0$ and a constant $\widetilde C\in[0,1)$ such that
--   $$\mathcal{F}(T)\le\widetilde C\,\mathcal{F}(0)$$
--   for every regular solution $u$ of (1.12)–(1.14).
--
--   This is the step "as in the case of boundary feedback" by which the paper passes from the observability estimate (4.26) and the dissipation estimate (4.1) to the exponential stability of Theorem 1.3.
--
--   **Formalization Note** The condition that every connected component of $\Omega$ has a point of $\Gamma_D$ in its closure is added (see Proposition 4.2).
-- source:
--   Nicaise, Pignotti, Stability and Instability Results of the Wave Equation with a Delay Term in the Boundary or Internal Feedbacks, SIAM J. Control Optim. 45 (2006), p. 1579, §4, last paragraph of the proof of Proposition 4.3 (referring to p. 1573, proof of Theorem 1.1)

import Mathlib
import Definitions.Def_NicaiseDelayWave_InternalStab_InternalDampingProblem

namespace NicaiseDelayWave.InternalStab

open MeasureTheory

theorem contraction_step {n : ℕ} (hn : 1 ≤ n) (D : NicaiseDelayWave.Shared.MixedDomain n)
    (hcomp : ∀ x ∈ D.Ω, (closure (connectedComponentIn D.Ω x) ∩ D.ΓD).Nonempty)
    (v : EuclideanSpace ℝ (Fin n) → ℝ) (α : ℝ) (hv : ConvexMultiplier D v α)
    (ω : Set (EuclideanSpace ℝ (Fin n))) (hω : IsInteriorNbhdΓN D ω)
    (a : EuclideanSpace ℝ (Fin n) → ℝ) (ha : IsDampingCoefficient D a)
    (a0 : ℝ) (ha0 : 0 < a0) (haω : ∀ᵐ x ∂(volume.restrict ω), a0 < a x)
    (μ1 μ2 τ ξ : ℝ) (hμ1 : 0 < μ1) (hμ2 : 0 < μ2) (hτ : 0 < τ) (h18 : μ2 < μ1)
    (h110 : τ * μ2 < ξ ∧ ξ < τ * (2 * μ1 - μ2)) :
    ∃ T : ℝ, 0 < T ∧ ∃ Ct : ℝ, 0 ≤ Ct ∧ Ct < 1 ∧
      ∀ u : EuclideanSpace ℝ (Fin n) → ℝ → ℝ, IsRegularSolution D a μ1 μ2 τ u →
        energyF D a ξ τ u T ≤ Ct * energyF D a ξ τ u 0 := by sorry

end NicaiseDelayWave.InternalStab

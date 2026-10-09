-- Prove2me | Theorems.Thm_ImpulsiveISS_FixedDwell_zero_input_KL_bound
-- name    : ImpulsiveISS.FixedDwell.zero_input_KL_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T17:45:04.40033+00:00
-- url     : https://prove2.me/theorems/4dbfefdb-b947-4d18-8660-a745bbc9d55b
-- title:
--   Proof of Theorem 1, p. 8 — for u ≡ 0, V(x(t)) ≤ β₂(V(φ₀), t − t₀) with β₂ ∈ KL
-- statement:
--   Assume the hypotheses of Theorem 1: an impulsive system with an ISS-Lyapunov function $V$ in max form with flow rate $\varphi\in\mathcal P$, jump rate $\alpha\in\mathcal P$, and $\theta,\delta>0$ satisfying (3.7). Let $T$ be an impulse sequence in $S_\theta$. Then there is $\beta_2\in\mathcal{KL}$ such that every trajectory with zero input $u\equiv0$ satisfies
--   $$V(x(t))\le\beta_2\big(V(x_0),t\big)\qquad\text{for all }x_0\in X,\ t\ge0 .$$
--
--   This is the zero-input half of the proof of Theorem 1: the Lyapunov function decays along every unforced trajectory at a rate that depends only on its initial value. The function $\beta_2$ may depend on the impulse sequence (Remark 2).
--
--   **Formalization Note** The initial time is $t_0=0$, so $t-t_0=t$. $\beta_2$ is quantified after the impulse sequence and before the initial state.
-- source:
--   Dashkovskiy and Mironchenko, Input-to-state stability of nonlinear impulsive systems, arXiv:1212.5481v1, p. 8, proof of Theorem 1, the display V(x(t)) ≤ β₂(V(φ₀), t − t₀) before (3.16)

import Mathlib
import Definitions.Def_SmallGainISS_Lyapunov_Gains
import Definitions.Def_ProcessingNetworks_LyapunovCriteria_DiniDerivative
import Definitions.Def_ImpulsiveISS_FixedDwell_Setting

open scoped NNReal
open Filter Topology
open SmallGainISS.Lyapunov ProcessingNetworks.LyapunovCriteria

namespace ImpulsiveISS.FixedDwell

/-- p. 8: under the hypotheses of Theorem 1, for every impulse sequence in `S_θ` there is
`β₂ ∈ 𝒦𝓛` (depending on the sequence) with `V(x(t)) ≤ β₂(V(x₀), t)` for all `x₀` and `t ≥ 0`
when `u ≡ 0`. -/
theorem zero_input_KL_bound {X U : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
    (S : System X U) (hS : IsImpulsiveSystem S)
    (V : X → ℝ≥0) (ψ₁ ψ₂ γ α φ : ℝ≥0 → ℝ≥0) (hV : IsISSLyapunovMax S V ψ₁ ψ₂ γ α φ)
    (hφ : IsPosDef φ) (θ δ : ℝ) (hθ : 0 < θ) (hδ : 0 < δ) (h37 : DwellCondition α φ θ δ)
    (τ : ℕ → ℝ) (hτ : InSTheta θ τ) :
    ∃ β₂ : ℝ≥0 → ℝ≥0 → ℝ≥0, IsKL β₂ ∧
      ∀ (x₀ : X) (t : ℝ), 0 ≤ t →
        V (traj S τ x₀ (fun _ => (0 : U)) t) ≤ β₂ (V x₀) t.toNNReal := by sorry

end ImpulsiveISS.FixedDwell

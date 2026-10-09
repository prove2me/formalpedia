-- Prove2me | Theorems.Thm_ImpulsiveISS_AvgDwell_flow_estimate
-- name    : ImpulsiveISS.AvgDwell.flow_estimate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T18:32:00.743666+00:00
-- url     : https://prove2.me/theorems/8a60cf46-630c-44cb-b51b-2aae703ad2b1
-- title:
--   Proof of Theorem 5, p. 12: exponential bound on an impulse-free flow piece
-- statement:
--   Let $V$ satisfy the max-form exponential Lyapunov conditions with continuous rate $c$, and let $x$ be the state at the start of an impulse-free flow piece of duration $T\ge0$. Suppose the admissible input has norm at most $M$ at every nonnegative time and $V(\phi_c(s,x,u))\ge\gamma(M)$ throughout $0\le s<T$. Then the state at the endpoint satisfies
--   $$V(\phi_c(T,x,u))\le e^{-cT}V(x).$$
--
--   This is the flow estimate used between successive impulses in the proof of Theorem 5. Continuity includes the endpoint, which may be a pre-jump state.
--
--   **Formalization Note** The system is represented by its continuous transition map and jump map. The upper-right Dini derivative has extended-real values. A duration $T$ and its initial state encode the source's interval $[t_i^k,t_{i+1}^k]$ after shifting the input.
-- source:
--   Dashkovskiy and Mironchenko, Input-to-state stability of nonlinear impulsive systems, arXiv:1212.5481v1, p. 12, proof of Theorem 5, (3.32) and display immediately after it

import Mathlib
import Definitions.Def_ImpulsiveISS_AvgDwell_Setting

open scoped NNReal

namespace ImpulsiveISS.AvgDwell

/-- Proof of Theorem 5, p. 12, (3.32) and the following display: the
exponential estimate on one impulse-free flow piece, including its endpoint. -/
theorem flow_estimate {X U : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
    (S : ImpulsiveISS.FixedDwell.System X U) (V : X → ℝ≥0) (ψ₁ ψ₂ γ : ℝ≥0 → ℝ≥0)
    (c d : ℝ) (x : X) (u : ℝ → U) (M : ℝ≥0) (T : ℝ)
    (hS : ImpulsiveISS.FixedDwell.IsImpulsiveSystem S)
    (hV : IsExpLyapunov S V ψ₁ ψ₂ γ c d)
    (hd : d ≠ 0)
    (hu : ImpulsiveISS.FixedDwell.IsPCInput u)
    (hM : ∀ s : ℝ, 0 ≤ s → ‖u s‖₊ ≤ M)
    (hT : 0 ≤ T)
    (hhigh : ∀ s : ℝ, 0 ≤ s → s < T → γ M ≤ V (S.flow s x u)) :
    (V (S.flow T x u) : ℝ) ≤ Real.exp (-c * T) * (V x : ℝ) := by sorry

end ImpulsiveISS.AvgDwell

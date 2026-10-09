-- Prove2me | Theorems.Thm_ImpulsiveISS_AvgDwell_excursion_estimate
-- name    : ImpulsiveISS.AvgDwell.excursion_estimate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T18:31:23.962988+00:00
-- url     : https://prove2.me/theorems/8d6d4c20-9a94-4a2d-9fe0-ee6110362077
-- title:
--   Proof of Theorem 5, p. 12: exponential estimate on a strict above-threshold excursion
-- statement:
--   Fix a sequence of impulses and a bounded admissible input of norm at most $M$. Let $0\le a\le t$. If $V(x(a))\ge\gamma(M)$ and $V(x(s))>\gamma(M)$ for every $a<s\le t$, then
--   $$V(x(t))\le e^{-dN(t,a)-c(t-a)}V(x(a)).$$
--
--   The factor counts precisely the impulses in $(a,t]$ and combines their jumps with decay along the intervening flows. It is the estimate used on an above-threshold excursion in the proof of Theorem 5.
--
--   **Formalization Note** The strict inequality after $a$ repairs the printed $\ge/<$ excursion split: a jump can land exactly on the threshold without obeying the multiplicative jump estimate. The count is a natural number cast to a real in the exponential.
-- source:
--   Dashkovskiy and Mironchenko, Input-to-state stability of nonlinear impulsive systems, arXiv:1212.5481v1, p. 12, proof of Theorem 5, display after (3.32)

import Mathlib
import Definitions.Def_ImpulsiveISS_AvgDwell_Setting

open scoped NNReal

namespace ImpulsiveISS.AvgDwell

/-- Proof of Theorem 5, p. 12, display after (3.32), on a strict
above-threshold excursion; the strict inequality excludes a threshold landing. -/
theorem excursion_estimate {X U : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
    (S : ImpulsiveISS.FixedDwell.System X U) (V : X → ℝ≥0) (ψ₁ ψ₂ γ : ℝ≥0 → ℝ≥0)
    (c d : ℝ) (τ : ℕ → ℝ) (x₀ : X) (u : ℝ → U) (M : ℝ≥0)
    (a t : ℝ)
    (hS : ImpulsiveISS.FixedDwell.IsImpulsiveSystem S)
    (hV : IsExpLyapunov S V ψ₁ ψ₂ γ c d)
    (hd : d ≠ 0)
    (hτ : ImpulsiveISS.FixedDwell.IsImpulseSeq τ)
    (hu : ImpulsiveISS.FixedDwell.IsPCInput u)
    (hM : ∀ s : ℝ, 0 ≤ s → ‖u s‖₊ ≤ M)
    (ha : 0 ≤ a) (hat : a ≤ t)
    (hstart : γ M ≤ V (traj S τ x₀ u a))
    (hhigh : ∀ s : ℝ, a < s → s ≤ t → γ M < V (traj S τ x₀ u s)) :
    (V (traj S τ x₀ u t) : ℝ) ≤
      Real.exp (-d * (count τ t a : ℝ) - c * (t - a)) *
        (V (traj S τ x₀ u a) : ℝ) := by sorry

end ImpulsiveISS.AvgDwell

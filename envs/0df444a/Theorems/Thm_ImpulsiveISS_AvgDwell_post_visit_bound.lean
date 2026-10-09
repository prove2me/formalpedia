-- Prove2me | Theorems.Thm_ImpulsiveISS_AvgDwell_post_visit_bound
-- name    : ImpulsiveISS.AvgDwell.post_visit_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T18:31:44.061571+00:00
-- url     : https://prove2.me/theorems/c3b1cd3d-7de1-4ac5-817d-0d82f6e3a61a
-- title:
--   Proof of Theorem 5, p. 12: uniform bound after a threshold visit
-- statement:
--   Suppose $h>0$ is dominated by a function in $\mathcal L$, and let $C_\lambda=\sup_{r\ge0}h(r)$. For any trajectory with admissible input bounded by $M$ and an impulse sequence in $S[h]$, if some time $a\in[0,t]$ has $V(x(a))\le\gamma(M)$, then
--   $$V(x(t))\le C_\lambda\max\{1,e^{-d}\}\gamma(M).$$
--
--   This is the input-controlled part of the uniform ISS estimate after the first visit to the threshold.
--
--   **Formalization Note** The domination by a decreasing nonnegative function makes the range of $h$ nonempty and bounded above, so its real supremum has the intended value. The factor $\max\{1,e^{-d}\}$ covers a visit occurring at an impulse.
-- source:
--   Dashkovskiy and Mironchenko, Input-to-state stability of nonlinear impulsive systems, arXiv:1212.5481v1, p. 12, proof of Theorem 5, two displays after (3.34)

import Mathlib
import Definitions.Def_ImpulsiveISS_AvgDwell_Setting

open scoped NNReal

namespace ImpulsiveISS.AvgDwell

/-- Proof of Theorem 5, p. 12, last display: the uniform bound after a
visit to the input threshold. -/
theorem post_visit_bound {X U : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
    (S : ImpulsiveISS.FixedDwell.System X U) (V : X → ℝ≥0) (ψ₁ ψ₂ γ : ℝ≥0 → ℝ≥0)
    (c d : ℝ) (h : ℝ≥0 → ℝ) (g : ℝ≥0 → ℝ≥0)
    (τ : ℕ → ℝ) (x₀ : X) (u : ℝ → U) (M : ℝ≥0) (t : ℝ)
    (hS : ImpulsiveISS.FixedDwell.IsImpulsiveSystem S)
    (hV : IsExpLyapunov S V ψ₁ ψ₂ γ c d)
    (hd : d ≠ 0)
    (hh : ∀ r, 0 < h r)
    (hg : ImpulsiveISS.FixedDwell.IsL g)
    (hdom : ∀ r, h r ≤ (g r : ℝ))
    (hτ : IsGADT τ c d h)
    (hu : ImpulsiveISS.FixedDwell.IsPCInput u)
    (hM : ∀ s : ℝ, 0 ≤ s → ‖u s‖₊ ≤ M)
    (ht : 0 ≤ t)
    (hvisit : ∃ a : ℝ, 0 ≤ a ∧ a ≤ t ∧ V (traj S τ x₀ u a) ≤ γ M) :
    (V (traj S τ x₀ u t) : ℝ) ≤
      height h * max 1 (Real.exp (-d)) * (γ M : ℝ) := by sorry

end ImpulsiveISS.AvgDwell

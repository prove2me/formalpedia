-- Prove2me | Theorems.Thm_ImpulsiveISS_AvgDwell_initial_phase
-- name    : ImpulsiveISS.AvgDwell.initial_phase
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T18:31:15.011031+00:00
-- url     : https://prove2.me/theorems/cf1d54ad-92f5-4154-8ea2-f40abec132c5
-- title:
--   Proof of Theorem 5, p. 12: dwell-time bound before reaching the input threshold
-- statement:
--   Let $h>0$ be dominated by $g\in\mathcal L$, and let an impulse sequence satisfy the generalized average dwell-time condition for $h$. For an admissible input bounded by $M$, suppose the trajectory stays strictly above $\gamma(M)$ from time $0$ through time $t\ge0$. Then
--   $$V(x(t))\le h(t)V(x_0),\qquad \psi_1(\|x(t)\|)\le g(t)\psi_2(\|x_0\|).$$
--
--   This is the initial-phase estimate (3.33)–(3.34) and its comparison-function consequence. It supplies the part of the eventual ISS estimate controlled by the initial state.
--
--   **Formalization Note** The second inequality states the source's inverse-$\psi_1$ bound without introducing a separate inverse: it is equivalent because $\psi_1\in\mathcal K_\infty$. The result is stated on the strict above-threshold stretch; at a jump onto the threshold the next bound applies.
-- source:
--   Dashkovskiy and Mironchenko, Input-to-state stability of nonlinear impulsive systems, arXiv:1212.5481v1, p. 12, proof of Theorem 5, (3.33)–(3.34) and paragraph following

import Mathlib
import Definitions.Def_ImpulsiveISS_AvgDwell_Setting

open scoped NNReal

namespace ImpulsiveISS.AvgDwell

/-- Proof of Theorem 5, p. 12, (3.33)–(3.34): decay until the first
visit to the input threshold, stated on the strict above-threshold stretch. -/
theorem initial_phase {X U : Type*}
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
    (hhigh : ∀ s : ℝ, 0 ≤ s → s ≤ t → γ M < V (traj S τ x₀ u s)) :
    (V (traj S τ x₀ u t) : ℝ) ≤ h t.toNNReal * (V x₀ : ℝ) ∧
      (ψ₁ ‖traj S τ x₀ u t‖₊ : ℝ) ≤
        (g t.toNNReal : ℝ) * (ψ₂ ‖x₀‖₊ : ℝ) := by sorry

end ImpulsiveISS.AvgDwell

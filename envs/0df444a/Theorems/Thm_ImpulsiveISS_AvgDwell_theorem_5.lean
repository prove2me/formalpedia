-- Prove2me | Theorems.Thm_ImpulsiveISS_AvgDwell_theorem_5
-- name    : ImpulsiveISS.AvgDwell.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T18:31:54.527118+00:00
-- url     : https://prove2.me/theorems/8698448d-0c98-4824-a438-8c88a5375c8c
-- title:
--   Theorem 5 (corrected): uniform ISS under generalized average dwell time
-- statement:
--   Let a real-Banach-space impulsive system admit a continuous max-form exponential ISS-Lyapunov function $V$ with comparison functions $\psi_1,\psi_2,\gamma\in\mathcal K_\infty$, continuous rate $c\in\mathbb R$, and jump rate $d\in\mathbb R\setminus\{0\}$. Let $h:\mathbb R_+\to(0,\infty)$ be dominated pointwise by some $g\in\mathcal L$. Define $S[h]$ by
--   $$-dN(t,s)-c(t-s)\le\log h(t-s)\quad\text{for every }t\ge s\ge0,$$
--   where $N(t,s)$ counts the impulses in $(s,t]$. Then the system is **uniformly input-to-state stable** over $S[h]$: one pair $\beta\in\mathcal{KL}$ and $\gamma'\in\mathcal K_\infty$, independent of the impulse sequence, initial state, and input, bounds every trajectory by
--   $$\|x(t)\|\le\beta(\|x_0\|,t)+\gamma'(M)$$
--   for every uniform bound $M$ on the input norm.
--
--   The theorem identifies the generalized average dwell-time condition under which the Lyapunov rates yield a common ISS estimate for all admissible impulse sequences.
--
--   **Formalization Note** This is a corrected statement: Proposition 3.2's max-form jump bound is used in place of Definition 4's implication-form jump clause. The printed theorem is false because a jump from $V<\gamma(\|\xi\|)$ can send the zero state to $1$ under an arbitrarily small constant input while satisfying its stated hypotheses. The model uses $(\phi_c,J)$ rather than a generator and mild solutions, fixes initial time $0$, and requires the first impulse strictly after $0$. The Lie derivative is extended-real, and input size is an arbitrary bound $M$. The source's $d\ne0$ remains explicit.
-- source:
--   Dashkovskiy and Mironchenko, Input-to-state stability of nonlinear impulsive systems, arXiv:1212.5481v1, p. 11, Theorem 5; corrected jump condition from p. 6, Proposition 3.2

import Mathlib
import Definitions.Def_ImpulsiveISS_AvgDwell_Setting

open scoped NNReal

namespace ImpulsiveISS.AvgDwell

/-- Theorem 5, p. 11, corrected with the max-form jump clause of Proposition
3.2, p. 6: one ISS pair works uniformly over all sequences in `S[h]`. -/
theorem theorem_5 {X U : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
    (S : ImpulsiveISS.FixedDwell.System X U) (V : X → ℝ≥0) (ψ₁ ψ₂ γ : ℝ≥0 → ℝ≥0)
    (c d : ℝ) (h : ℝ≥0 → ℝ) (g : ℝ≥0 → ℝ≥0)
    (hS : ImpulsiveISS.FixedDwell.IsImpulsiveSystem S)
    (hV : IsExpLyapunov S V ψ₁ ψ₂ γ c d)
    (hd : d ≠ 0)
    (hh : ∀ r, 0 < h r)
    (hg : ImpulsiveISS.FixedDwell.IsL g)
    (hdom : ∀ r, h r ≤ (g r : ℝ)) :
    UniformISS S (fun τ => IsGADT τ c d h) := by sorry

end ImpulsiveISS.AvgDwell

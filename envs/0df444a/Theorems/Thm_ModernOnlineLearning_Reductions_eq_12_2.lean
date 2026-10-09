-- Prove2me | Theorems.Thm_ModernOnlineLearning_Reductions_eq_12_2
-- name    : ModernOnlineLearning.Reductions.eq_12_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:32:15.007999+00:00
-- url     : https://prove2.me/theorems/9908bb2e-ee38-4c0d-bb10-9bf1931ad489
-- title:
--   Equation (12.2) — split linearized regret at the unconstrained prediction
-- statement:
--   In a projected run of Algorithm 12.1, let $u\in V$ be fixed and let $g_t$ satisfy the subgradient inequality for $\ell_t$ at $x_t$ on $V$. For $T\ge1$,
--   $$\sum_{t=1}^{T}(\ell_t(x_t)-\ell_t(u))\le\sum_{t=1}^{T}g_t(x_t-u)=\sum_{t=1}^{T}\bigl(g_t(z_t-u)+g_t(x_t-z_t)\bigr).$$
--   This isolates the term that the surrogate loss must compensate when $z_t$ lies outside $V$.
--
--   **Formalization Note** The loss subgradient inequality is restricted to $V$, which suffices because the comparator lies in $V$. The ambient space is finite-dimensional, and the book's round index starts at one.
-- source:
--   Orabona, arXiv:1912.13213v10, equation (12.2), proof of Theorem 12.5, p. 196

import Mathlib
import Definitions.Def_ModernOnlineLearning_Reductions_Setting

namespace ModernOnlineLearning.Reductions

/-- Orabona, equation (12.2), p. 196: first-order ModernOnlineLearning.OGD.regret and its split at `z_t`. -/
theorem eq_12_2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (V W : Set E) (hV : V.Nonempty)
    (hclosed : IsClosed V) (hconv : Convex ℝ V) (hVW : V ⊆ W)
    (loss : ℕ → E → ℝ) (z x : ℕ → E) (g q : ℕ → E →L[ℝ] ℝ)
    (T : ℕ) (hT : 1 ≤ T) (hRun : IsProjectedRun V W loss z x g q T)
    (u : E) (hu : u ∈ V) :
    ModernOnlineLearning.OGD.regret loss x u T ≤ ∑ t ∈ Finset.Icc 1 T, g t (x t - u) ∧
      (∑ t ∈ Finset.Icc 1 T, g t (x t - u)) =
        ∑ t ∈ Finset.Icc 1 T, (g t (z t - u) + g t (x t - z t)) := by sorry

end ModernOnlineLearning.Reductions

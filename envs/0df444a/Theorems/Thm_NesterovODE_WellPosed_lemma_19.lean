-- Prove2me | Theorems.Thm_NesterovODE_WellPosed_lemma_19
-- name    : NesterovODE.WellPosed.lemma_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:41:12.811483+00:00
-- url     : https://prove2.me/theorems/1b3d8c26-799f-4d0b-b3fc-459d3f29367e
-- title:
--   Lemma 19, p. 31 — local uniqueness at zero
-- statement:
--   For $f\in\mathcal F_\infty$, equation (3) with a specified initial position $x_0$ and zero initial velocity has at most one local solution near $t=0$. If $X,Y$ are solutions on a common interval $[0,a)$, then
--   $$
--   \exists\varepsilon\in(0,a]\quad
--   \forall t\in[0,\varepsilon),\ X(t)=Y(t).
--   $$
--   This is the local uniqueness component of Theorem 1.
--
--   **Formalization Note** Equality concerns the nonnegative time interval. A function $\mathbb R\to\mathbb R^n$ may take arbitrary values at negative times, so global equality of such representatives is not asserted.
-- source:
--   Su, Boyd, Candès, A Differential Equation for Modeling Nesterov's Accelerated Gradient Method, arXiv:1503.01243v2, p. 31, Lemma 19

import Mathlib
import Definitions.Def_NesterovODE_WellPosed_Setting

namespace NesterovODE.WellPosed

/-- Lemma 19, p. 31: two local solutions agree near the singular initial time. -/
theorem lemma_19 {n : ℕ} (f : E n → ℝ) (x₀ : E n)
    (a : ℝ) (X V Y W : ℝ → E n)
    (hf : ∃ L : NNReal, IsFL f L)
    (hX : IsLocalSolution f x₀ a X V)
    (hY : IsLocalSolution f x₀ a Y W) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ a ∧ Set.EqOn X Y (Set.Ico 0 ε) := by sorry

end NesterovODE.WellPosed

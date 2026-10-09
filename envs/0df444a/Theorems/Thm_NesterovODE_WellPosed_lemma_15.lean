-- Prove2me | Theorems.Thm_NesterovODE_WellPosed_lemma_15
-- name    : NesterovODE.WellPosed.lemma_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:41:17.878908+00:00
-- url     : https://prove2.me/theorems/5dd0c672-0cc4-478c-8b29-7736f15ce6b9
-- title:
--   Lemma 15, p. 28 — velocity bound within the smoothing interval
-- statement:
--   Let $f\in\mathcal F_L$ with $L>0$, and let $X_\delta$ solve (31) from $x_0$. If $0<\delta<\sqrt{6/L}$, then
--   $$
--   M_\delta(\delta)\le
--   \frac{\|\nabla f(x_0)\|}{1-L\delta^2/6},
--   \qquad
--   M_\delta(\delta)=\sup_{0<u\le\delta}\frac{\|\dot X_\delta(u)\|}{u}.
--   $$
--   This is the first uniform control on smoothed velocities near the singular initial time.
--
--   **Formalization Note** The bound is stated for each $0<u\le\delta$, which is equivalent to the stated supremum bound. Positivity of $L$ and $\delta$ comes from the definitions and the page's standing assumptions.
-- source:
--   Su, Boyd, Candès, A Differential Equation for Modeling Nesterov's Accelerated Gradient Method, arXiv:1503.01243v2, p. 28, Lemma 15

import Mathlib
import Definitions.Def_NesterovODE_WellPosed_Setting

namespace NesterovODE.WellPosed

/-- Lemma 15, p. 28: the first velocity bound for the smoothed equation. -/
theorem lemma_15 {n : ℕ} (f : E n → ℝ) (L : NNReal) (x₀ : E n)
    (δ : ℝ) (X V : ℝ → E n)
    (hf : IsFL f L) (hX : IsSmoothedSolution f δ x₀ X V)
    (hδ : δ < Real.sqrt (6 / (L : ℝ))) :
    ∀ u : ℝ, 0 < u → u ≤ δ →
      ‖V u‖ / u ≤ ‖gradient f x₀‖ / (1 - (L : ℝ) * δ ^ 2 / 6) := by sorry

end NesterovODE.WellPosed

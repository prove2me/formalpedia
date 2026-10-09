-- Prove2me | Theorems.Thm_NesterovODE_WellPosed_lemma_17
-- name    : NesterovODE.WellPosed.lemma_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:41:06.031671+00:00
-- url     : https://prove2.me/theorems/23eb4f64-e3a6-424a-8559-bc0b13997c04
-- title:
--   Lemma 17, p. 29 — velocity bound beyond the smoothing interval
-- statement:
--   Let $f\in\mathcal F_L$, and let $X_\delta$ solve (31) from $x_0$. If $\delta<\sqrt{6/L}$ and $\delta<t<\sqrt{12/L}$, then
--   $$
--   M_\delta(t)\le
--   \frac{(5-L\delta^2/6)\|\nabla f(x_0)\|}
--   {4(1-L\delta^2/6)(1-Lt^2/12)}.
--   $$
--   Here $M_\delta(t)=\sup_{0<u\le t}\|\dot X_\delta(u)\|/u$. This extends the appendix's velocity control past $t=\delta$.
--
--   **Formalization Note** The conclusion bounds every quotient on $0<u\le t$, avoiding the default value of a real supremum on a set without an upper bound.
-- source:
--   Su, Boyd, Candès, A Differential Equation for Modeling Nesterov's Accelerated Gradient Method, arXiv:1503.01243v2, p. 29, Lemma 17

import Mathlib
import Definitions.Def_NesterovODE_WellPosed_Setting

namespace NesterovODE.WellPosed

/-- Lemma 17, p. 29: the velocity bound beyond the smoothing interval. -/
theorem lemma_17 {n : ℕ} (f : E n → ℝ) (L : NNReal) (x₀ : E n)
    (δ t : ℝ) (X V : ℝ → E n)
    (hf : IsFL f L) (hX : IsSmoothedSolution f δ x₀ X V)
    (hδ : δ < Real.sqrt (6 / (L : ℝ))) (hδt : δ < t)
    (ht : t < Real.sqrt (12 / (L : ℝ))) :
    ∀ u : ℝ, 0 < u → u ≤ t →
      ‖V u‖ / u ≤
        (5 - (L : ℝ) * δ ^ 2 / 6) * ‖gradient f x₀‖ /
          (4 * (1 - (L : ℝ) * δ ^ 2 / 6) * (1 - (L : ℝ) * t ^ 2 / 12)) := by sorry

end NesterovODE.WellPosed

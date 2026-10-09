-- Prove2me | Theorems.Thm_NesterovODE_WellPosed_lemma_16
-- name    : NesterovODE.WellPosed.lemma_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:41:09.080359+00:00
-- url     : https://prove2.me/theorems/0e1fcece-bc20-4767-8dbe-6af3d146d090
-- title:
--   Lemma 16, p. 29 — gradient variation along a smoothed solution
-- statement:
--   Let $f\in\mathcal F_L$, let $X_\delta$ solve the smoothed equation (31) from $x_0$, and let $u>0$. Write $M_\delta(u)=\sup_{0<v\le u}\|\dot X_\delta(v)\|/v$. Then
--   $$
--   \|\nabla f(X_\delta(u))-\nabla f(x_0)\|\le \tfrac12 L M_\delta(u)u^2.
--   $$
--   This controls the change in the gradient through the initial velocity growth.
--
--   **Formalization Note** The statement uses any upper bound $B$ on every quotient $\|\dot X_\delta(v)\|/v$ for $0<v\le u$, and concludes the same inequality with $B$. This pointwise form represents the supremum without a default value on an unbounded set.
-- source:
--   Su, Boyd, Candès, A Differential Equation for Modeling Nesterov's Accelerated Gradient Method, arXiv:1503.01243v2, p. 29, Lemma 16

import Mathlib
import Definitions.Def_NesterovODE_WellPosed_Setting

namespace NesterovODE.WellPosed

/-- Lemma 16, p. 29: gradient variation along a smoothed trajectory. -/
theorem lemma_16 {n : ℕ} (f : E n → ℝ) (L : NNReal) (x₀ : E n)
    (δ : ℝ) (X V : ℝ → E n) (u B : ℝ)
    (hf : IsFL f L) (hX : IsSmoothedSolution f δ x₀ X V)
    (hu : 0 < u) (hB : ∀ v : ℝ, 0 < v → v ≤ u → ‖V v‖ / v ≤ B) :
    ‖gradient f (X u) - gradient f x₀‖ ≤
      (1 / 2 : ℝ) * (L : ℝ) * B * u ^ 2 := by sorry

end NesterovODE.WellPosed

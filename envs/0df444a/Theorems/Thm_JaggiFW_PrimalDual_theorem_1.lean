-- Prove2me | Theorems.Thm_JaggiFW_PrimalDual_theorem_1
-- name    : JaggiFW.PrimalDual.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:03:48.482221+00:00
-- url     : https://prove2.me/theorems/45f743be-0f10-468e-b0c1-4402f7d5dffc
-- title:
--   Theorem 1 — primal convergence of four Frank–Wolfe variants
-- statement:
--   Let $f$ be convex and continuously differentiable on a compact convex domain $D$, with finite curvature constant $C_f$. Start any of Algorithms 1–4 at $x^{(0)}\in D$, and let $x^*$ minimize $f$ on $D$. If the approximate linear subproblems have quality parameter $\delta\ge0$, then every iterate with $k\ge1$ satisfies
--
--   $$f(x^{(k)})-f(x^*)\le\frac{2C_f}{k+2}(1+\delta).$$
--
--   This is the paper's uniform primal convergence rate for its four update rules.
--
--   **Formalization Note** The theorem quantifies over an unbounded run, since the bound holds for every $k\ge1$. It uses the exact supremum $C_f$, whose finiteness is made explicit. The ambient Hilbert space is generalized to a real normed space via the Fréchet derivative, and convexity is required only on $D$. For Algorithm 1 the exact oracle corresponds to $\delta=0$; allowing a larger nonnegative $\delta$ merely loosens its bound.
-- source:
--   Jaggi, Revisiting Frank-Wolfe: Projection-Free Sparse Convex Optimization, ICML 2013 (JMLR W&CP 28), https://proceedings.mlr.press/v28/jaggi13.html, PDF p. 4, Theorem 1

import Mathlib
import Definitions.Def_JaggiFW_PrimalDual_Setting

namespace JaggiFW.PrimalDual

/-- Theorem 1 (primal convergence), page 4. -/
theorem theorem_1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : Set E) (hDc : IsCompact D) (hDconv : Convex ℝ D)
    (f : E → ℝ) (hfC1 : ContDiff ℝ 1 f) (hfconv : ConvexOn ℝ D f)
    (hCf : BddAbove (curvatureSet f D))
    (xstar : E) (hxstar : xstar ∈ D) (hmin : ∀ y ∈ D, f xstar ≤ f y)
    (δ : ℝ) (hδ : 0 ≤ δ) (v : Variant) (x s : ℕ → E) (hx0 : x 0 ∈ D)
    (hrun : ∀ k, IsFWStep f D δ (curvatureConst f D) v x s k) :
    ∀ k : ℕ, 1 ≤ k →
      f (x k) - f xstar ≤ 2 * curvatureConst f D / ((k : ℝ) + 2) * (1 + δ) := by sorry

end JaggiFW.PrimalDual

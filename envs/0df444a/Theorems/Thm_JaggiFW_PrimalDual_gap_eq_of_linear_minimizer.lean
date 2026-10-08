-- Prove2me | Theorems.Thm_JaggiFW_PrimalDual_gap_eq_of_linear_minimizer
-- name    : JaggiFW.PrimalDual.gap_eq_of_linear_minimizer
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:03:43.262244+00:00
-- url     : https://prove2.me/theorems/559af8d4-5d3a-4cfe-8d5f-b491caae3912
-- title:
--   §2 — the linear subproblem computes the gap
-- statement:
--   Let $D$ be a compact domain, let $x,s\in D$, and suppose that $s$ minimizes the linearized objective $t\mapsto f'(x)(t)$ over $D$. Then the duality gap is attained at $s$:
--
--   $$g(x)=f'(x)(x-s).$$
--
--   Thus an exact Frank–Wolfe linear subproblem returns a numerical optimality certificate along with its atom.
--
--   **Formalization Note** The paper's standing convexity and continuous-differentiability assumptions are omitted because this identity uses only the linear derivative at $x$. The chosen point $x$ makes the real supremum nonempty, and compactness bounds it.
-- source:
--   Jaggi, Revisiting Frank-Wolfe: Projection-Free Sparse Convex Optimization, ICML 2013 (JMLR W&CP 28), https://proceedings.mlr.press/v28/jaggi13.html, PDF p. 2, §2 “The Duality Gap and Certificates”, paragraph beginning “While the value”

import Mathlib
import Definitions.Def_JaggiFW_PrimalDual_Setting

namespace JaggiFW.PrimalDual

/-- The exact linear subproblem computes the gap, page 2 after equation (2). -/
theorem gap_eq_of_linear_minimizer {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : Set E) (hDc : IsCompact D) (f : E → ℝ)
    (x s : E) (hx : x ∈ D) (hs : s ∈ D)
    (hsmin : ∀ ŝ ∈ D, fderiv ℝ f x s ≤ fderiv ℝ f x ŝ) :
    dualityGap f D x = fderiv ℝ f x (x - s) := by sorry

end JaggiFW.PrimalDual

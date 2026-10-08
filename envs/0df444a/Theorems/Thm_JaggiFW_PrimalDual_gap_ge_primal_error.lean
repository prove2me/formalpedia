-- Prove2me | Theorems.Thm_JaggiFW_PrimalDual_gap_ge_primal_error
-- name    : JaggiFW.PrimalDual.gap_ge_primal_error
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:03:35.709214+00:00
-- url     : https://prove2.me/theorems/eaf947dd-f270-4058-89dc-d0369b9fa8aa
-- title:
--   §2 — linearization and primal-error certificate
-- statement:
--   Let $D$ be a compact convex domain, let $f$ be a convex, continuously differentiable objective, and let $x^*\in D$ minimize $f$ on $D$. At every feasible $x,s\in D$, the linearization at $x$ lies below $f(s)$. Consequently, the duality gap $g(x)$ bounds the primal error:
--
--   $$f(x)+f'(x)(s-x)\le f(s),\qquad f(x)-f(x^*)\le g(x).$$
--
--   The gap is therefore a certificate for the quality of a feasible iterate, even when the optimal value is unknown.
--
--   **Formalization Note** The derivative pairing is written as $f'(x)$ on a real normed space. Convexity is required on $D$; continuous differentiability is kept from the paper's standing assumptions.
-- source:
--   Jaggi, Revisiting Frank-Wolfe: Projection-Free Sparse Convex Optimization, ICML 2013 (JMLR W&CP 28), https://proceedings.mlr.press/v28/jaggi13.html, PDF p. 2, §2 “The Duality Gap and Certificates”, paragraph following (2)

import Mathlib
import Definitions.Def_JaggiFW_PrimalDual_Setting

namespace JaggiFW.PrimalDual

/-- The linearization inequality and the certificate following equation (2), page 2. -/
theorem gap_ge_primal_error {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : Set E) (hDc : IsCompact D) (hDconv : Convex ℝ D)
    (f : E → ℝ) (hfC1 : ContDiff ℝ 1 f) (hfconv : ConvexOn ℝ D f)
    (xstar : E) (hxstar : xstar ∈ D) (hmin : ∀ y ∈ D, f xstar ≤ f y) :
    (∀ x ∈ D, ∀ s ∈ D, f x + fderiv ℝ f x (s - x) ≤ f s) ∧
      (∀ x ∈ D, f x - f xstar ≤ dualityGap f D x) := by sorry

end JaggiFW.PrimalDual

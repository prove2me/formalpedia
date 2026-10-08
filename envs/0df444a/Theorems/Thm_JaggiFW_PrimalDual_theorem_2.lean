-- Prove2me | Theorems.Thm_JaggiFW_PrimalDual_theorem_2
-- name    : JaggiFW.PrimalDual.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:03:44.188823+00:00
-- url     : https://prove2.me/theorems/b41f3a00-a2a7-4786-a27f-f0705c1afba9
-- title:
--   Theorem 2 — a small duality gap within K iterations
-- statement:
--   Let $f$ be convex and continuously differentiable on a compact convex domain $D$, with finite curvature constant $C_f$. Run one of the paper's four Frank–Wolfe algorithms from $x^{(0)}\in D$ with linear-subproblem quality $\delta\ge0$. If $K\ge2$, some iterate indexed by $1\le\widehat k\le K$ satisfies
--
--   $$g(x^{(\widehat k)})\le\frac{2\beta C_f}{K+2}(1+\delta),\qquad\beta=\frac{27}{8}.$$
--
--   The result guarantees an observable optimality certificate within the stated number of iterations, rather than only a bound on the unknown primal error.
--
--   **Formalization Note** The run has the paper's steps $k=0,\ldots,K$; $x^{(0)}$ is feasible, while later feasibility follows from the update rules. The exact curvature supremum is used with its boundedness stated explicitly. The Hilbert-space pairing is expressed through the Fréchet derivative on a real normed space, and convexity is required only on $D$. For Algorithm 1 the exact oracle is represented for every $\delta\ge0$, including its source value $\delta=0$.
-- source:
--   Jaggi, Revisiting Frank-Wolfe: Projection-Free Sparse Convex Optimization, ICML 2013 (JMLR W&CP 28), https://proceedings.mlr.press/v28/jaggi13.html, PDF p. 4, Theorem 2

import Mathlib
import Definitions.Def_JaggiFW_PrimalDual_Setting

namespace JaggiFW.PrimalDual

/-- Theorem 2 (primal-dual convergence), page 4. -/
theorem theorem_2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : Set E) (hDc : IsCompact D) (hDconv : Convex ℝ D)
    (f : E → ℝ) (hfC1 : ContDiff ℝ 1 f) (hfconv : ConvexOn ℝ D f)
    (hCf : BddAbove (curvatureSet f D))
    (xstar : E) (hxstar : xstar ∈ D) (hmin : ∀ y ∈ D, f xstar ≤ f y)
    (δ : ℝ) (hδ : 0 ≤ δ) (v : Variant) (x s : ℕ → E) (hx0 : x 0 ∈ D)
    (K : ℕ) (hK : 2 ≤ K)
    (hrun : ∀ k, k ≤ K → IsFWStep f D δ (curvatureConst f D) v x s k) :
    ∃ khat ∈ Finset.Icc 1 K,
      dualityGap f D (x khat) ≤
        2 * (27 / 8 : ℝ) * curvatureConst f D / ((K : ℝ) + 2) * (1 + δ) := by sorry

end JaggiFW.PrimalDual

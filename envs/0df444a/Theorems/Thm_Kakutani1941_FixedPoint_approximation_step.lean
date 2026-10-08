-- Prove2me | Theorems.Thm_Kakutani1941_FixedPoint_approximation_step
-- name    : Kakutani1941.FixedPoint.approximation_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:15:37.580719+00:00
-- url     : https://prove2.me/theorems/dc830677-a376-4d1f-bb9f-461a290a77de
-- title:
--   Proof of Theorem 1 — arbitrarily fine barycentric approximation
-- statement:
--   Let $S$ be an $r$-dimensional closed simplex in Euclidean space, and let $\Phi(x)$ be a nonempty subset of $S$ for every $x\in S$. For every $\varepsilon>0$ there are points $x,x_0,\ldots,x_r\in S$, selections $y_i\in\Phi(x_i)$, and weights $\lambda_i\ge0$ summing to one for which
--
--   $$\|x_i-x\|\le\varepsilon,\qquad x=\sum_{i=0}^{r}\lambda_i x_i=\sum_{i=0}^{r}\lambda_i y_i.$$
--
--   The result records the approximate fixed points obtained from finer barycentric subdivisions. The error bounds the mesh of the selected cell. Convexity and upper semi-continuity of the values enter later in the proof.
--
--   **Formalization Note** The page selects $y_i$ from each value; its implicit nonemptiness assumption is explicit here. The simplex is the convex hull of $r+1$ affinely independent vertices.
-- source:
--   Kakutani, A generalization of Brouwer's fixed point theorem, Duke Math. J. 8 (1941), pp. 457–458, proof of Theorem 1, https://doi.org/10.1215/s0012-7094-41-00838-4

import Mathlib
import Definitions.Def_Kakutani1941_FixedPoint_ApproximationData

namespace Kakutani1941.FixedPoint

/-- Proof of Theorem 1, pp. 457–458: barycentric data from a sufficiently fine subdivision. -/
theorem approximation_step {m r : ℕ} (v : Fin (r + 1) → EuclideanSpace ℝ (Fin m))
    (hv : AffineIndependent ℝ v)
    (Φ : EuclideanSpace ℝ (Fin m) → Set (EuclideanSpace ℝ (Fin m)))
    (hΦsub : ∀ x ∈ convexHull ℝ (Set.range v), Φ x ⊆ convexHull ℝ (Set.range v))
    (hΦne : ∀ x ∈ convexHull ℝ (Set.range v), (Φ x).Nonempty) :
    ∀ ε : ℝ, 0 < ε →
      ApproximationData (convexHull ℝ (Set.range v)) Φ r ε := by sorry

end Kakutani1941.FixedPoint

-- Prove2me | Theorems.Thm_Kakutani1941_FixedPoint_theorem_1
-- name    : Kakutani1941.FixedPoint.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:15:19.5504+00:00
-- url     : https://prove2.me/theorems/d8ca0ede-74dd-4808-bf95-ab8fc863621c
-- title:
--   Theorem 1 — fixed point of a correspondence on a closed simplex
-- statement:
--   Let $S$ be an $r$-dimensional closed simplex in Euclidean space. Suppose that for every $x\in S$, $\Phi(x)$ is a nonempty closed convex subset of $S$, and that $\Phi$ is upper semi-continuous in the sequential sense. Then
--
--   $$\exists x_0\in S\quad x_0\in\Phi(x_0).$$
--
--   This is Kakutani's simplex extension of Brouwer's fixed-point theorem and is the source's principal theorem before the general convex-set Corollary.
--
--   **Formalization Note** The page calls its value family $\mathfrak R(S)$, which includes the empty set; nonemptiness is stated separately because the proof chooses a point from each value. An $r$-simplex is the convex hull of $r+1$ affinely independent vertices.
-- source:
--   Kakutani, A generalization of Brouwer's fixed point theorem, Duke Math. J. 8 (1941), p. 457, Theorem 1, https://doi.org/10.1215/s0012-7094-41-00838-4

import Mathlib
import Definitions.Def_Kakutani1941_FixedPoint_ClosedConvexSubset
import Definitions.Def_Kakutani1941_FixedPoint_UpperSemicontinuous

namespace Kakutani1941.FixedPoint

/-- Theorem 1, p. 457: Kakutani's fixed-point theorem on a closed simplex. -/
theorem theorem_1 {m r : ℕ} (v : Fin (r + 1) → EuclideanSpace ℝ (Fin m))
    (hv : AffineIndependent ℝ v)
    (Φ : EuclideanSpace ℝ (Fin m) → Set (EuclideanSpace ℝ (Fin m)))
    (hΦ : ∀ x ∈ convexHull ℝ (Set.range v),
      IsClosedConvexSubset (convexHull ℝ (Set.range v)) (Φ x))
    (hΦne : ∀ x ∈ convexHull ℝ (Set.range v), (Φ x).Nonempty)
    (husc : IsUpperSemicontinuous (convexHull ℝ (Set.range v)) Φ) :
    ∃ x₀ ∈ convexHull ℝ (Set.range v), x₀ ∈ Φ x₀ := by sorry

end Kakutani1941.FixedPoint

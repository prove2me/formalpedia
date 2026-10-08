-- Prove2me | Theorems.Thm_Kakutani1941_FixedPoint_enclosing_simplex
-- name    : Kakutani1941.FixedPoint.enclosing_simplex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:02:59.731442+00:00
-- url     : https://prove2.me/theorems/50a433fa-e267-462b-9751-a5ab58550f1d
-- title:
--   Proof of the Corollary — enclosing a bounded set in a simplex
-- statement:
--   Every bounded set $S$ in $m$-dimensional Euclidean space lies in an $m$-dimensional closed simplex: there are affinely independent vertices $v_0,\ldots,v_m$ such that
--
--   $$S\subseteq\operatorname{conv}\{v_0,\ldots,v_m\}.$$
--
--   This supplies the larger simplex $S'$ used in the proof of Kakutani's Corollary. The assertion also applies to the empty set.
--
--   **Formalization Note** The simplex is represented as the convex hull of a finite range, with affine independence imposing full dimension.
-- source:
--   Kakutani, A generalization of Brouwer's fixed point theorem, Duke Math. J. 8 (1941), p. 458, proof of the Corollary, https://doi.org/10.1215/s0012-7094-41-00838-4

import Mathlib

namespace Kakutani1941.FixedPoint

/-- Proof of the Corollary, p. 458: a bounded set fits in a closed full simplex. -/
theorem enclosing_simplex {m : ℕ} {S : Set (EuclideanSpace ℝ (Fin m))}
    (hSbounded : Bornology.IsBounded S) :
    ∃ v : Fin (m + 1) → EuclideanSpace ℝ (Fin m),
      AffineIndependent ℝ v ∧ S ⊆ convexHull ℝ (Set.range v) := by sorry

end Kakutani1941.FixedPoint

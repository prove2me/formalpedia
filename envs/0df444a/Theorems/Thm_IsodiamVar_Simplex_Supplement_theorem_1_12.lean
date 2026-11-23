-- Prove2me | Theorems.Thm_IsodiamVar_Simplex_Supplement_theorem_1_12
-- name    : IsodiamVar.Simplex.Supplement.theorem_1_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T12:53:03.110378+00:00
-- url     : https://prove2.me/theorems/d24f4083-50dc-4555-a497-39ac089c1333
-- title:
--   Theorem 1.12 — Jung’s exact enclosing radius and extremal unit simplex
-- statement:
--   Let $K\subseteq\mathbb R^n$ be compact with diameter one, and put $r_n=\sqrt{n/(2n+2)}$. Then
--
--   $$\exists q\in\mathbb R^n,\qquad K\subseteq\overline B_{r_n}(q).$$
--
--   If there is no enclosing closed ball of any nonnegative radius strictly smaller than $r_n$, then $K$ contains the vertices of a unit regular $n$-simplex:
--
--   $$\exists x_0,\ldots,x_n\in K,\qquad |x_i-x_j|=1\quad(i\ne j).$$
--
--   This includes the exact radius and the full extremal conclusion. It does not assert that $K$ consists only of these vertices. No finiteness, convexity or full-dimensionality hypothesis is imposed on $K$. Compactness guarantees that its real-valued diameter is not the default value for an unbounded set.
--
--   Differences from the source:
--   - encoding: Compact Euclidean sets of diameter one, and absence of any smaller enclosing ball → Metric.diam K = 1 and explicit quantification over all centers and nonnegative radii below rn n; the published regular-simplex predicate; reason: Compactness makes real diameter safe and the statement keeps simplex containment rather than equality of sets.
-- source:
--   Lim & McCann, Geometrical bounds for the variance and recentered moments, arXiv:2001.11851v1, p. 7, Theorem 1.12

import Definitions.Def_IsodiamVar_Simplex_Defs

open MeasureTheory

namespace IsodiamVar.Simplex.Supplement

/-- Theorem 1.12, p. 7; proof p. 16. Compact K need not be finite or full-dimensional. -/
theorem theorem_1_12 {n : ℕ} (K : Set (E n)) (hK : IsCompact K)
    (hdiam : Metric.diam K = 1) :
    (∃ q : E n, K ⊆ Metric.closedBall q (rn n)) ∧
    ((¬ ∃ q : E n, ∃ r : ℝ, 0 ≤ r ∧ r < rn n ∧ K ⊆ Metric.closedBall q r) →
      ∃ x : Fin (n + 1) → E n, IsRegularSimplex x 1 ∧ Set.range x ⊆ K) := by sorry

end IsodiamVar.Simplex.Supplement

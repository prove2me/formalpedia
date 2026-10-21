-- Prove2me | Theorems.Thm_IsodiamVar_Simplex_proposition_3_1_b
-- name    : IsodiamVar.Simplex.proposition_3_1_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:47:20.211843+00:00
-- url     : https://prove2.me/theorems/423ed314-772f-43bc-97b6-1fe0b203fd3c
-- title:
--   Proposition 3.1(b) — equality geometry at the simplex radius
-- statement:
--   Let $K$ lie on the centered sphere in $\mathbb R^n$ of radius $r_n=\sqrt{n/(2n+2)}$, with diameter at most one. If the origin belongs to the closed convex hull of $K$, then
--
--   $$
--   K=\{x_0,\ldots,x_n\}
--   $$
--
--   for the vertices of a unit regular $n$-simplex. The set equality rules out additional points on the sphere.
-- source:
--   Lim & McCann, Geometrical bounds for the variance and recentered moments, arXiv:2001.11851v1, p. 13, Proposition 3.1(b)

import Mathlib
import Definitions.Def_IsodiamVar_Simplex_Defs

namespace IsodiamVar.Simplex

/-- Proposition 3.1(b): the borderline case consists of exactly the simplex vertices. -/
theorem proposition_3_1_b (n : ℕ) (K : Set (E n))
    (hKs : K ⊆ Metric.sphere (0 : E n) (rn n)) (hKd : Metric.diam K ≤ 1)
    (hKh : (0 : E n) ∈ closedConvexHull ℝ K) :
    ∃ x : Fin (n + 1) → E n, IsRegularSimplex x 1 ∧ K = Set.range x := by sorry

end IsodiamVar.Simplex

-- Prove2me | Theorems.Thm_GeometryOfGraphs_Clique_volume_count
-- name    : GeometryOfGraphs.Clique.volume_count
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:11:10.689988+00:00
-- url     : https://prove2.me/theorems/a757d213-5660-4213-a947-7e1805c204d2
-- title:
--   Proposition 5.4 proof — equilateral sets have at most 2ᵈ points
-- statement:
--   If $n\ge1$ points lie pairwise at norm-distance one in a $d$-dimensional real normed space, then
--
--   $$
--   n\le2^d.
--   $$
--
--   This is the cardinality consequence of the volume comparison in Proposition 5.4 and supplies the lower bound on the dimension of a complete graph.
--
--   **Formalization Note** The assertion applies even when the convex hull has zero ambient volume. In that case the volume argument must be applied in the affine hull of the points.
-- source:
--   N. Linial, E. London, Y. Rabinovich, The geometry of graphs and some of its algorithmic applications, Combinatorica 15 (1995), p. 231, proof of Proposition 5.4, volume-count paragraph

import Definitions.Def_GeometryOfGraphs_Clique_isoDim

namespace GeometryOfGraphs.Clique

/-- The cardinality consequence of the volume count in Proposition 5.4, p. 231. -/
theorem volume_count {n d : ℕ} (hn : 0 < n) (N : (Fin d → ℝ) → ℝ)
    (hN : IsNormFun N) (x : Fin n → (Fin d → ℝ))
    (hx : ∀ i j, i ≠ j → N (x i - x j) = 1) :
    n ≤ 2 ^ d := by sorry

end GeometryOfGraphs.Clique

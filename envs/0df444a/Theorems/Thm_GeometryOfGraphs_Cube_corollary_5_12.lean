-- Prove2me | Theorems.Thm_GeometryOfGraphs_Cube_corollary_5_12
-- name    : GeometryOfGraphs.Cube.corollary_5_12
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:39:56.823982+00:00
-- url     : https://prove2.me/theorems/9a079165-4683-493a-a719-f34759f91b9c
-- title:
--   Corollary 5.12 — isometric dimension of the m-cube
-- statement:
--   Let $m\geq1$ and let the $m$-cube be the graph of binary strings of length $m$, adjacent when they differ in one coordinate. Its isometric dimension is exactly $m$:
--
--   $$
--   \dim(m\text{-Cube})=m.
--   $$
--
--   Thus no isometric realization in any real normed space of lower dimension is possible, while an isometric realization in dimension $m$ exists.
--
--   **Formalization Note** The printed proof uses an isometric $2m$-cycle for the lower bound when $m\geq2$; the $m=1$ case is the two-vertex graph and is included directly.
-- source:
--   N. Linial, E. London, Y. Rabinovich, The geometry of graphs and some of its algorithmic applications, Combinatorica 15 (1995), p. 233, Corollary 5.12; https://doi.org/10.1007/BF01200757

import Definitions.Def_GeometryOfGraphs_Cube_IsometricDimension
import Definitions.Def_GeometryOfGraphs_Cube_Hypercube

set_option autoImplicit false

namespace GeometryOfGraphs.Cube

/-- Corollary 5.12: the `m`-cube has isometric dimension `m`. -/
theorem corollary_5_12 (m : ℕ) (hm : 1 ≤ m) : isoDim (hypercube m) = m := by sorry

end GeometryOfGraphs.Cube

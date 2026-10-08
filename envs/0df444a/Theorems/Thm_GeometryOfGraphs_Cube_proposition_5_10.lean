-- Prove2me | Theorems.Thm_GeometryOfGraphs_Cube_proposition_5_10
-- name    : GeometryOfGraphs.Cube.proposition_5_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:39:56.807623+00:00
-- url     : https://prove2.me/theorems/d07d5d6b-de0a-4e84-ad94-cad8bc95fe98
-- title:
--   Proposition 5.10 — isometric dimension of an even cycle
-- statement:
--   For an integer $m\geq2$, the cycle on $2m$ vertices has isometric dimension $m$:
--
--   $$
--   \dim(C_{2m})=m.
--   $$
--
--   This supplies the lower bound for the cube through its isometric even-cycle subgraph. The condition $m\geq2$ gives an ordinary cycle with at least four vertices.
-- source:
--   N. Linial, E. London, Y. Rabinovich, The geometry of graphs and some of its algorithmic applications, Combinatorica 15 (1995), p. 233, Proposition 5.10; https://doi.org/10.1007/BF01200757

import Definitions.Def_GeometryOfGraphs_Cube_IsometricDimension

set_option autoImplicit false

namespace GeometryOfGraphs.Cube

/-- Proposition 5.10: the even cycle has isometric dimension half its length. -/
theorem proposition_5_10 (m : ℕ) (hm : 2 ≤ m) :
    isoDim (SimpleGraph.cycleGraph (2 * m)) = m := by sorry

end GeometryOfGraphs.Cube

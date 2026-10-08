-- Prove2me | Theorems.Thm_GeometryOfGraphs_Cube_isometric_subgraph_monotonicity
-- name    : GeometryOfGraphs.Cube.isometric_subgraph_monotonicity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:40:16.323184+00:00
-- url     : https://prove2.me/theorems/52e56e26-d500-4925-8b0d-c3ac9905b23a
-- title:
--   Section 5.1 — isometric-subgraph dimension monotonicity
-- statement:
--   Suppose $J$ and $G$ are finite connected graphs and a vertex map $f:V(J)\to V(G)$ preserves every graph distance. Then
--
--   $$
--   \dim(J)\leq\dim(G).
--   $$
--
--   Thus an isometric subgraph supplies a lower bound on the dimension of its containing graph.
-- source:
--   N. Linial, E. London, Y. Rabinovich, The geometry of graphs and some of its algorithmic applications, Combinatorica 15 (1995), p. 230, Section 5.1, paragraph beginning “J is an isometric subgraph”; https://doi.org/10.1007/BF01200757

import Definitions.Def_GeometryOfGraphs_Cube_IsometricDimension

set_option autoImplicit false

namespace GeometryOfGraphs.Cube

/-- The dimension of an isometric subgraph is at most the dimension of its host graph. -/
theorem isometric_subgraph_monotonicity {V W : Type*}
    [Fintype V] [Fintype W] (G : SimpleGraph V) (J : SimpleGraph W)
    (hG : G.Connected) (hJ : J.Connected) (f : W → V)
    (hf : ∀ x y, G.dist (f x) (f y) = J.dist x y) :
    isoDim J ≤ isoDim G := by sorry

end GeometryOfGraphs.Cube

-- Prove2me | Theorems.Thm_GeometryOfGraphs_Cube_cycle_in_cube
-- name    : GeometryOfGraphs.Cube.cycle_in_cube
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:39:29.272889+00:00
-- url     : https://prove2.me/theorems/f81aef4c-e7a7-4e26-b935-cf4b0e1fca1c
-- title:
--   Proof of Corollary 5.12 — isometric even cycle in the cube
-- statement:
--   For $m\geq2$, the cycle $C_{2m}$ embeds in the $m$-cube by a vertex map $f$ preserving all pairwise graph distances:
--
--   $$
--   d_{m\text{-Cube}}(f(i),f(j))=d_{C_{2m}}(i,j)\qquad\text{for all }i,j.
--   $$
--
--   This is the subgraph used in the lower-bound sentence of Corollary 5.12.
-- source:
--   N. Linial, E. London, Y. Rabinovich, The geometry of graphs and some of its algorithmic applications, Combinatorica 15 (1995), p. 233, proof of Corollary 5.12, second sentence; https://doi.org/10.1007/BF01200757

import Definitions.Def_GeometryOfGraphs_Cube_Hypercube

set_option autoImplicit false

namespace GeometryOfGraphs.Cube

/-- The `2m`-cycle is an isometric subgraph of the `m`-cube. -/
theorem cycle_in_cube (m : ℕ) (hm : 2 ≤ m) :
    ∃ f : Fin (2 * m) → (Fin m → Bool), ∀ i j,
      (hypercube m).dist (f i) (f j) =
        (SimpleGraph.cycleGraph (2 * m)).dist i j := by sorry

end GeometryOfGraphs.Cube

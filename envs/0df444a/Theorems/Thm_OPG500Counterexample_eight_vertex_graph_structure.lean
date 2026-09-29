-- Prove2me | Theorems.Thm_OPG500Counterexample_eight_vertex_graph_structure
-- name    : OPG500Counterexample.eight_vertex_graph_structure
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-07T04:07:47.165646+00:00
-- url     : https://prove2.me/theorems/e22fbdd7-a649-4c23-a6c8-e342a48654b8
-- title:
--   The structure and peripheral cycles of the fixed graph
-- statement:
--   For the fixed eighteen-edge graph $H$ on eight vertices:
--
--   1. $H$ is 3-connected: it has at least four vertices and deletion of any set of fewer than three vertices leaves a connected induced graph.
--   2. A simple cycle of $H$ is peripheral if and only if its vertex set is one of the twelve triples frozen in `peripheralTriples`.
--
--   Thus the theorem classifies every cycle of $H$, not only the four triangles contained in the core.
-- source:
--   Candidate C10, graph and peripheral-cycle classification: https://github.com/vibemathing/problem-opg-500-geodesic-cycles/blob/a41fe59b4535851ea55f6e868e938b9aaf81e924/research/artifacts/candidates/opg500-a01-c10/tight-rank.md

import Definitions.Def_opg500_eight_vertex_graph

namespace OPG500Counterexample

/-- The fixed graph is 3-connected, and its peripheral cycles are exactly the
twelve frozen apex triangles, classified by their vertex sets. -/
theorem eight_vertex_graph_structure :
    IsThreeConnected H ∧
      ∀ C : Cycle H,
        C.IsPeripheral ↔ C.walk.support.toFinset ∈ peripheralTriples := by sorry

end OPG500Counterexample

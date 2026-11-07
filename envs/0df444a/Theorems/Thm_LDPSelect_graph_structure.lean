-- Prove2me | Theorems.Thm_LDPSelect_graph_structure
-- name    : LDPSelect.graph_structure
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:54:21.197202+00:00
-- url     : https://prove2.me/theorems/a9d36c44-72c1-4747-8547-3c53b6eb13d4
-- title:
--   Proof of Theorem 3, graph structure — components complete multipartite iff no induced $P_4$ or paw
-- statement:
--   Let $G$ be a finite simple graph. Every connected component of $G$ is complete multipartite if and only if $G$ has no induced $P_4$ and no induced paw (a triangle with a pendant edge).
--
--   Differences from the source:
--   - encoding: an induced P4, an induced paw → an induced embedding of `pathGraph 4`, resp. of the graph on Fin 4 with edges 12, 03, 13, 23; reason: the paper's paw {14, 23, 24, 34} shifted by one
-- source:
--   Chen, Wang, When Does Private Data Collection Need Interaction? Online Selection under Local Differential Privacy, STOC 2027 submission (manuscript sha256 2e2d6157…), proof of Theorem 3, Graph structure, p.8 (pdf p.9)

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LDPSelect

/-- Chen, Wang, *When Does Private Data Collection Need Interaction? Online Selection under Local Differential Privacy*, STOC 2027 submission (manuscript sha256 2e2d6157…), proof of Theorem 3, Graph structure, p.8.

A finite simple graph has every connected component complete multipartite if and only if it has no
induced `P4` and no induced paw.

**Formalization Note.** The paw is the triangle on `1, 2, 3` with the pendant edge `03`, the paper's edges
`{14, 23, 24, 34}` shifted by one (p.8). An induced subgraph is an induced embedding `↪g`. -/
theorem graph_structure {V : Type*} [Fintype V] (G : SimpleGraph V) :
    (∀ C : G.ConnectedComponent, C.toSimpleGraph.IsCompleteMultipartite) ↔
      IsEmpty (SimpleGraph.pathGraph 4 ↪g G) ∧
      IsEmpty (SimpleGraph.fromEdgeSet
        ({s(1, 2), s(0, 3), s(1, 3), s(2, 3)} : Set (Sym2 (Fin 4))) ↪g G) := by sorry

end LDPSelect

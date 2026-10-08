-- Prove2me | Theorems.Thm_MatousekLP_Integrality_incidenceMatrix_totallyUnimodular
-- name    : MatousekLP.Integrality.incidenceMatrix_totallyUnimodular
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T10:28:42.204342+00:00
-- url     : https://prove2.me/theorems/b74fc86d-c2f0-479b-b7e1-9d83da1f7cec
-- title:
--   Lemma 8.2.5 — the incidence matrix of a bipartite graph is totally unimodular
-- statement:
--   Let $G = (X \,\dot\cup\, Y, E)$ be a finite bipartite graph and let $A$ be its vertex–edge incidence matrix, with $a_{ve} = 1$ if $v \in e$ and $a_{ve} = 0$ otherwise. Then
--   $$
--   A \text{ is totally unimodular,}
--   $$
--   that is, every square submatrix of $A$ has determinant $0$, $1$ or $-1$.
--
--   Together with Lemma 8.2.4 this shows that the matching and vertex-cover integer programs of a bipartite graph have the same optima as their LP relaxations, which is the link between total unimodularity and König's theorem.
--
--   **Formalization Note** Rows are indexed by the vertex type and columns by the edge set of $G$; bipartiteness is the existence of some bipartition `IsBipartite G`.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 146, Lemma 8.2.5

import Mathlib
import Definitions.Def_MatousekLP_Integrality_BipartiteGraph
import Definitions.Def_MatousekLP_Integrality_IncidenceMatrix

namespace MatousekLP.Integrality

theorem incidenceMatrix_totallyUnimodular {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : IsBipartite G) :
    (incidenceMatrix G).IsTotallyUnimodular := by sorry

end MatousekLP.Integrality

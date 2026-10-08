-- Prove2me | Theorems.Thm_MatousekLP_Integrality_konig
-- name    : MatousekLP.Integrality.konig
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T10:28:25.678805+00:00
-- url     : https://prove2.me/theorems/d6915922-c91e-4a6f-a7e3-901055aface5
-- title:
--   Theorem 8.2.2 — König's theorem
-- statement:
--   Let $G = (V, E)$ be a finite bipartite graph. Then the size of a maximum matching in $G$ equals the size of a minimum vertex cover of $G$:
--   $$
--   \max\{ |M| : M \subseteq E \text{ a matching} \} \;=\; \min\{ |C| : C \subseteq V \text{ a vertex cover} \}.
--   $$
--   Here a matching is a set of edges in which each vertex is incident to at most one edge, and a vertex cover is a set of vertices meeting every edge.
--
--   König's theorem is the prototypical combinatorial min–max theorem obtained from linear programming duality together with total unimodularity; Hall's theorem follows from it.
--
--   **Formalization Note** Both extremes are stated as attained: there exist a matching $M$ of maximum size and a vertex cover $C$ of minimum size with $|M| = |C|$. No supremum or infimum is used. Vertex covers are Mathlib's `SimpleGraph.IsVertexCover`.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 144, Theorem 8.2.2 (König's theorem); definitions of matching and vertex cover p. 143

import Mathlib
import Definitions.Def_MatousekLP_Integrality_BipartiteGraph

namespace MatousekLP.Integrality

theorem konig {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hG : IsBipartite G) :
    ∃ M : Finset (Sym2 V), IsMatching G M ∧
      (∀ M' : Finset (Sym2 V), IsMatching G M' → M'.card ≤ M.card) ∧
      ∃ C : Finset V, G.IsVertexCover (C : Set V) ∧
        (∀ C' : Finset V, G.IsVertexCover (C' : Set V) → C.card ≤ C'.card) ∧
        M.card = C.card := by sorry

end MatousekLP.Integrality

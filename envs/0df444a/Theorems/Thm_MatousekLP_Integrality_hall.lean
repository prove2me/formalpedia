-- Prove2me | Theorems.Thm_MatousekLP_Integrality_hall
-- name    : MatousekLP.Integrality.hall
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T10:27:38.477149+00:00
-- url     : https://prove2.me/theorems/74604637-92dc-4010-9240-21252c758183
-- title:
--   Theorem 8.2.1 — Hall's theorem
-- statement:
--   Let $G = (V, E)$ be a finite bipartite graph with bipartition $V = X \,\dot\cup\, Y$. For a set $T \subseteq X$ let
--   $$
--   N(T) = \{ w \in Y : \{v, w\} \in E \text{ for some } v \in T \}
--   $$
--   be its neighbourhood. If $|N(T)| \ge |T|$ holds for every $T \subseteq X$, then $G$ has a matching that covers all vertices in $X$, that is, a matching $M$ such that every $x \in X$ is an end-vertex of some edge of $M$.
--
--   Hall's condition is also necessary, but the book states and proves only this direction, as a consequence of König's theorem.
--
--   **Formalization Note** The bipartition is given explicitly as finite sets $X, Y$ (`IsBipartition G X Y`); the matching is a finite set of edges of $G$.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 144, Theorem 8.2.1 (Hall's theorem)

import Mathlib
import Definitions.Def_MatousekLP_Integrality_BipartiteGraph

namespace MatousekLP.Integrality

theorem hall {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (X Y : Finset V) (hXY : IsBipartition G X Y)
    (hN : ∀ T ⊆ X, T.card ≤ (neighborhood G Y T).card) :
    ∃ M : Finset (Sym2 V), IsMatching G M ∧ ∀ x ∈ X, ∃ e ∈ M, x ∈ e := by sorry

end MatousekLP.Integrality

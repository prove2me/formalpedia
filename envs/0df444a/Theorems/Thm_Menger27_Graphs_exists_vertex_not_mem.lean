-- Prove2me | Theorems.Thm_Menger27_Graphs_exists_vertex_not_mem
-- name    : Menger27.Graphs.exists_vertex_not_mem
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:18:10.47466+00:00
-- url     : https://prove2.me/theorems/feccd0d1-3fd5-4e70-b47b-7e60829356b8
-- title:
--   p. 102, proof of Satz δ — an irreducibly n-point connected graph with more than n edges has a vertex outside P ∪ Q
-- statement:
--   Let $K'$ be a finite simple graph on $V$, let $P, Q \subseteq V$ be disjoint, and let $n \ge 0$. Suppose $K'$ is irreducibly $n$-point connected between $P$ and $Q$ and has more than $n$ edges. Then $K'$ has a vertex $s$ that lies on an edge of $K'$ and belongs neither to $P$ nor to $Q$:
--   $$\exists\, s \notin P \cup Q,\ \exists\, t:\ st \in E(K') .$$
--
--   Menger writes: "Wir nehmen also an, der irreduzibel n-punktig zusammenhängende Raum K′ besitze den Grad g (> n). Offenbar enthält dann K′ ein punktförmiges Stück s, welches in der Menge P + Q nicht enthalten ist." This vertex is where the separating set of the next step is anchored.
--
--   Menger calls the claim obvious. If every vertex on an edge of $K'$ lay in $P \cup Q$, irreducibility would leave only edges between $P$ and $Q$, and the claim reduces to the statement that a bipartite graph whose vertex covers have at least $n$ vertices has a matching of $n$ edges, i.e. to Kőnig's theorem. Kőnig (1931) pointed out this gap in Menger's proof.
--
--   **Formalization Note.** Menger's *punktförmiges Stück* is a vertex of the graph; "in K′" is rendered as lying on an edge of $K'$, since the points of Menger's space are the points of its arcs. The degree is the number of edges.
-- source:
--   Menger, Zur allgemeinen Kurventheorie, Fund. Math. 10 (1927), p. 102, proof of Satz δ

import Mathlib
import Definitions.Def_Menger27_Graphs_Separation
import Definitions.Def_Menger27_Graphs_Parts

namespace Menger27.Graphs

theorem exists_vertex_not_mem {V : Type*} [Fintype V] [DecidableEq V] (K : SimpleGraph V)
    [DecidableRel K.Adj] (P Q : Finset V) (hPQ : Disjoint P Q) (n : ℕ)
    (hK : IrreduciblyNPointConnected K P Q n) (hgrad : n < K.edgeFinset.card) :
    ∃ s : V, s ∉ P ∧ s ∉ Q ∧ ∃ t : V, K.Adj s t := by sorry

end Menger27.Graphs

-- Prove2me | Theorems.Thm_OnlineThreeColorBounds_LowerBound_Supplement_neighborhood_offline_monochromatic
-- name    : OnlineThreeColorBounds.LowerBound.Supplement.neighborhood_offline_monochromatic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:38:05.10125+00:00
-- url     : https://prove2.me/theorems/22362c72-878f-44dd-9c59-4ddbffb920d0
-- title:
--   Lemma 3.1 — sides of neighborhood components are offline-monochromatic
-- statement:
--   Let $G$ be a three-colorable graph and $v$ a vertex of $G$, and let $G[N_G(v)]$ be the subgraph induced by the neighbors of $v$. Then $G[N_G(v)]$ is bipartite. Moreover, take any bipartition $b:N_G(v)\to\{0,1\}$ of $G[N_G(v)]$, any $x\in N_G(v)$, and any side $i\in\{0,1\}$. The set
--   $$S=\{\,y\in N_G(v) : y \text{ lies in the connected component of } x \text{ in } G[N_G(v)] \text{ and } b(y)=i\,\}$$
--   is an offline-monochromatic class of $G$: every proper coloring of $G$ with at most three colors gives all vertices of $S$ the same color.
--
--   Each side of every connected component of $G[N_G(v)]$ is such a set $S$, so this is the paper's statement. The lemma certifies that the classes maintained by the randomized algorithm of Theorem 1.2 are monochromatic in every three-coloring. Through Corollary 3.3, it bounds the number of labels sent to the child instance child-mono.
--
--   **Formalization Note** The two-coloring `b` ranges over all `Coloring Bool` of the induced graph `G.induce (G.neighborSet v)`. The component is given by `Reachable` in that graph. A proper coloring with at most three colors is a `G.Coloring (Fin 3)`.
--
--   Differences from the source:
--   - generalization: a (finite) graph G → a graph on an arbitrary vertex type V; reason: the statement makes no use of finiteness, and finite vertex types are a special case
--   - reading: the sides of the components of G[N_G(v)], which presuppose that G[N_G(v)] is bipartite → an explicit conclusion that G[N_G(v)] is 2-colorable, then every 2-coloring b and every side of every component; reason: the source uses this presupposition (the neighborhood of a vertex of a three-colorable graph is bipartite, §1.1, printed p. 1); stating it as a conclusion makes the statement non-vacuous
--   - encoding: proper three-coloring → Mathlib G.Coloring (Fin 3); reason: every proper coloring with at most three colors can be renamed into Fin 3, and renaming preserves equal colors
-- source:
--   Yaqiao Li, New bounds for online coloring three-colorable graphs, STOC 2027 submission #425 (October 2026), pinned submission PDF SHA256 ca491d3191fa544c55ed3f45022e4cb14e5570bbd8b8bfb36e98205a8a5c518a, Lemma 3.1, §3.4, printed p. 14 / PDF p. 15

import Definitions.Def_OnlineThreeColorBounds_LowerBound_Supplement_Graphs
set_option autoImplicit false

namespace OnlineThreeColorBounds.LowerBound.Supplement

/-- Lemma 3.1, printed p. 14 / PDF p. 15. In a three-colorable graph `G`, the neighborhood graph
`G[N(v)]` is bipartite, and for every two-coloring `b` of it, every vertex `x ∈ N(v)` and every
side `i`, the vertices of the component of `x` that `b` puts on side `i` form an
offline-monochromatic class of `G`. -/
theorem neighborhood_offline_monochromatic {V : Type*} (G : SimpleGraph V)
    (hG : G.Colorable 3) (v : V) :
    (G.induce (G.neighborSet v)).Colorable 2 ∧
      ∀ b : (G.induce (G.neighborSet v)).Coloring Bool, ∀ x : G.neighborSet v, ∀ i : Bool,
        OfflineMonochromatic G
          {y : V | ∃ hy : y ∈ G.neighborSet v,
            (G.induce (G.neighborSet v)).Reachable x ⟨y, hy⟩ ∧ b ⟨y, hy⟩ = i} := by sorry

end OnlineThreeColorBounds.LowerBound.Supplement

-- Prove2me | Theorems.Thm_NashWilliams61_TreePacking_lemma_2
-- name    : NashWilliams61.TreePacking.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:27:39.850048+00:00
-- url     : https://prove2.me/theorems/53b81548-76c0-418d-b867-2806d04059ff
-- title:
--   Lemma 2 — every connected graph has a spanning tree
-- statement:
--   Let $G$ be a finite multigraph without loops and $(W, F)$ a subgraph of $G$ (every edge of $F$ has both ends in $W$) that is connected: $W$ is non-empty and any two vertices of $W$ are joined by a path of $F$-edges. Then there is $T \subseteq F$ such that $(W, T)$ is a tree, i.e. $T$ is a spanning tree of $(W, F)$.
--
--   Together with Lemma 1 this gives the proof of necessity of Theorem 1.
--
--   **Formalization Note** "Connected" is spelled out as non-empty plus pairwise reachability by $F$-edges; the conclusion is the multigraph spanning-tree notion of the definition file.
-- source:
--   Nash-Williams, Edge-disjoint spanning trees of finite graphs, J. London Math. Soc. 36 (1961), p. 445, Lemma 2

import Mathlib
import Definitions.Def_NagamochiIbaraki_EdgeConn_Multigraph
import Definitions.Def_NashWilliams61_TreePacking_Graphs
open NagamochiIbaraki.EdgeConn

namespace NashWilliams61.TreePacking

/-- **Lemma 2** (Nash-Williams 1961, p. 445). Every connected graph has a spanning tree: if
`(W, F)` is a subgraph (every edge of `F` has both ends in `W`) with `W` non-empty and
every two vertices of `W` joined by a path of `F`-edges, then some `T ⊆ F` is a spanning
tree of `(W, F)`. -/
theorem lemma_2 {V E : Type} [DecidableEq V] [DecidableEq E] (ends : E → Sym2 V)
    (hloop : ∀ e, ¬ (ends e).IsDiag) (W : Finset V) (F : Finset E)
    (hF : ∀ e ∈ F, ∀ v ∈ ends e, v ∈ W) (hW : W.Nonempty)
    (hconn : ∀ u ∈ W, ∀ v ∈ W, (edgeGraph ends F).Reachable u v) :
    ∃ T : Finset E, IsSpanningTreeOn ends W F T := by sorry

end NashWilliams61.TreePacking

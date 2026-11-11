-- Prove2me | Theorems.Thm_MinorFreeSTC_Main_lemma_1
-- name    : MinorFreeSTC.Main.lemma_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:18:10.224557+00:00
-- url     : https://prove2.me/theorems/b05608ad-ba44-4945-9865-933e5d90289c
-- title:
--   Lemma 1 — unweighted forests admit 2H_n-diameter strong (2H_n, 2)-sparse partitions
-- statement:
--   Let $G$ be an unweighted forest on $n$ vertices (every edge of weight $1$, no cycles) and $H_n=\lceil\log_2n\rceil+1$. Then $G$ has a partition $\mathcal P$ of $V$ into clusters of strong diameter at most $2H_n$ such that every ball of radius
--   $$\frac{2H_n}{2H_n}=1$$
--   meets at most $2$ clusters, i.e. a $2H_n$-diameter strong $(2H_n,2)$-sparse partition.
--
--   This is the base case of the paper's construction of strong sparse partitions (via heavy-light decompositions); Lemma 2 lifts it to unweighted $K_r$-minor-free graphs.
--
--   Differences from the source:
--   - generalization: n-vertex unweighted forest (with the standing assumption that input graphs are connected, p. 14) → any finite unweighted acyclic WGraph, connected or not; reason: the lemma says 'forest' and Lemma 2's proof applies it to a disconnected forest F; the connected case (trees) is a special case
--   - encoding: unweighted graph → WGraph with every edge weight 1 (`Unweighted G`); reason: distances are then hop counts; same instances
--   - encoding: distances d_G, d_C, d_T and α·d_G(u, v) → values in [0, ∞] (`ℝ≥0∞`), α·d as `ENNReal.ofReal α * d`; reason: the published `WGraph.dist`/`distIn` convention; on connected graphs and connected clusters every distance is finite
-- source:
--   Filtser, Fletcher, Hershkowitz, Milenković, (1 + ϵ)-Distortion Spanning Tree Covers of Minor-Free Graphs with Size O(log log n), STOC 2027 submission (manuscript sha256 f475e254…), p. 16, Lemma 1

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_MinorFreeSTC_Main_Graphs
import Definitions.Def_MinorFreeSTC_Main_Covers

set_option autoImplicit false

open scoped ENNReal

namespace MinorFreeSTC.Main

open ARTreeCover

/-- **Lemma 1** (p. 16). Every `n`-vertex unweighted forest admits a `2H_n`-diameter strong
`(2H_n, 2)`-sparse partition. -/
theorem lemma_1 (V : Type) [Fintype V] [DecidableEq V] (G : WGraph V) (hunw : Unweighted G)
    (hforest : G.graph.IsAcyclic) :
    ∃ P : Finset (Finset V), IsStrongSparsePartition G P
      ((2 * Hn (Fintype.card V) : ℕ) : ℝ) ((2 * Hn (Fintype.card V) : ℕ) : ℝ) 2 := by sorry

end MinorFreeSTC.Main

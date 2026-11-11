-- Prove2me | Theorems.Thm_MinorFreeSTC_Main_lemma_2
-- name    : MinorFreeSTC.Main.lemma_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:18:19.711338+00:00
-- url     : https://prove2.me/theorems/8aa319b3-ab34-4a71-855a-203e5fdd2fc3
-- title:
--   Lemma 2 — unweighted K_r-minor-free graphs admit 2H_n-diameter strong (2H_n, 2κ_r)-sparse partitions
-- statement:
--   Let $r\ge4$ and let $G$ be a connected unweighted $n$-vertex graph with no $K_r$ minor; put $H_n=\lceil\log_2n\rceil+1$ and $\kappa_r=5\binom r2(r-3)$. Then $G$ has a partition into clusters of strong diameter at most $2H_n$ such that every ball of radius $1$ meets at most $2\kappa_r$ clusters: a
--   $$2H_n\text{-diameter strong }(2H_n,\ 2\kappa_r)\text{-sparse partition.}$$
--
--   This lifts Lemma 1 from forests to unweighted minor-free graphs using Theorem 6; Lemma 3 iterates it on quotient graphs.
--
--   Differences from the source:
--   - encoding: unweighted graph → WGraph with every edge weight 1 (`Unweighted G`); reason: distances are then hop counts; same instances
--   - encoding: graph (with the standing assumption 'we will assume all input graphs are connected', p. 14) → hypothesis `Connected G` (d_G(u, v) < ∞ for all u, v); reason: standing assumption of §3.1 made explicit
--   - encoding: distances d_G, d_C, d_T and α·d_G(u, v) → values in [0, ∞] (`ℝ≥0∞`), α·d as `ENNReal.ofReal α * d`; reason: the published `WGraph.dist`/`distIn` convention; on connected graphs and connected clusters every distance is finite
-- source:
--   Filtser, Fletcher, Hershkowitz, Milenković, (1 + ϵ)-Distortion Spanning Tree Covers of Minor-Free Graphs with Size O(log log n), STOC 2027 submission (manuscript sha256 f475e254…), p. 17, Lemma 2

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_MinorFreeSTC_Main_Graphs
import Definitions.Def_MinorFreeSTC_Main_Covers

set_option autoImplicit false

open scoped ENNReal

namespace MinorFreeSTC.Main

open ARTreeCover

/-- **Lemma 2** (p. 17). For `r ≥ 4`, every connected unweighted `n`-vertex `K_r`-minor-free
graph admits a `2H_n`-diameter strong `(2H_n, 2κ_r)`-sparse partition. -/
theorem lemma_2 (r : ℕ) (hr : 4 ≤ r) (V : Type) [Fintype V] [DecidableEq V] (G : WGraph V)
    (hunw : Unweighted G) (hconn : Connected G) (hG : MinorFree G r) :
    ∃ P : Finset (Finset V), IsStrongSparsePartition G P
      ((2 * Hn (Fintype.card V) : ℕ) : ℝ) ((2 * Hn (Fintype.card V) : ℕ) : ℝ)
      ((2 * kappa r : ℕ) : ℝ) := by sorry

end MinorFreeSTC.Main

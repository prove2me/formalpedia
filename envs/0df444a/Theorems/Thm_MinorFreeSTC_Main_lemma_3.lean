-- Prove2me | Theorems.Thm_MinorFreeSTC_Main_lemma_3
-- name    : MinorFreeSTC.Main.lemma_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:18:54.795862+00:00
-- url     : https://prove2.me/theorems/1f52245f-fc34-493c-93c2-2a949efcbb34
-- title:
--   Lemma 3 — unweighted K_r-minor-free graphs admit D_{n,t}-diameter strong (D_{n,t}/t, (2κ_r)^t)-sparse partitions
-- statement:
--   Let $t\in\mathbb N$, $r\ge4$, and let $G$ be a connected unweighted $n$-vertex graph with no $K_r$ minor. Put
--   $$D_{n,t}=(2H_n+1)^t-1 .$$
--   Then $G$ has a partition into clusters of strong diameter at most $D_{n,t}$ such that every ball of radius $D_{n,t}/(D_{n,t}/t)=t$ meets at most $(2\kappa_r)^t$ clusters: a $D_{n,t}$-diameter strong $(D_{n,t}/t,(2\kappa_r)^t)$-sparse partition.
--
--   This extends Lemma 2 to larger diameters by repeated contraction; Theorem 2 combines it with shortcut partitions.
--
--   **Formalization Note.** At $t=0$, $D_{n,0}=0$ and Lean's $0/0=0$ gives ball radius $0$; the statement then asks for the singleton partition with sparsity $1$, which holds.
--
--   Differences from the source:
--   - encoding: unweighted graph → WGraph with every edge weight 1 (`Unweighted G`); reason: distances are then hop counts; same instances
--   - encoding: graph (with the standing assumption 'we will assume all input graphs are connected', p. 14) → hypothesis `Connected G` (d_G(u, v) < ∞ for all u, v); reason: standing assumption of §3.1 made explicit
--   - encoding: distances d_G, d_C, d_T and α·d_G(u, v) → values in [0, ∞] (`ℝ≥0∞`), α·d as `ENNReal.ofReal α * d`; reason: the published `WGraph.dist`/`distIn` convention; on connected graphs and connected clusters every distance is finite
-- source:
--   Filtser, Fletcher, Hershkowitz, Milenković, (1 + ϵ)-Distortion Spanning Tree Covers of Minor-Free Graphs with Size O(log log n), STOC 2027 submission (manuscript sha256 f475e254…), p. 17, Lemma 3

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_MinorFreeSTC_Main_Graphs
import Definitions.Def_MinorFreeSTC_Main_Covers

set_option autoImplicit false

open scoped ENNReal

namespace MinorFreeSTC.Main

open ARTreeCover

/-- **Lemma 3** (p. 17). For every `t` and `r ≥ 4`, every connected unweighted `n`-vertex
`K_r`-minor-free graph admits a `D_{n,t}`-diameter strong `(D_{n,t}/t, (2κ_r)^t)`-sparse
partition, where `D_{n,t} = (2H_n + 1)^t − 1`. -/
theorem lemma_3 (t r : ℕ) (hr : 4 ≤ r) (V : Type) [Fintype V] [DecidableEq V] (G : WGraph V)
    (hunw : Unweighted G) (hconn : Connected G) (hG : MinorFree G r) :
    ∃ P : Finset (Finset V), IsStrongSparsePartition G P
      (((2 * Hn (Fintype.card V) + 1) ^ t - 1 : ℕ) : ℝ)
      ((((2 * Hn (Fintype.card V) + 1) ^ t - 1 : ℕ) : ℝ) / t)
      (((2 * kappa r) ^ t : ℕ) : ℝ) := by sorry

end MinorFreeSTC.Main

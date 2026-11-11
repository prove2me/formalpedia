-- Prove2me | Theorems.Thm_MinorFreeSTC_Main_theorem_7
-- name    : MinorFreeSTC.Main.theorem_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:18:33.265348+00:00
-- url     : https://prove2.me/theorems/3b35a064-b42e-4e1c-b266-203c18bf3c07
-- title:
--   Theorem 7 — edge-weighted K_r-minor-free graphs admit (ϵ, 2^{O(r log r)}/ϵ)-shortcut partitions for every ϵ ∈ (0,1) ([CCL+24])
-- statement:
--   There is a universal constant $c>0$ such that every connected edge-weighted graph $G$ with no $K_r$ minor and every $\epsilon\in(0,1)$ admit an $(\epsilon,h)$-shortcut partition with
--   $$h=\frac{2^{\,c\,r\log_2 r}}{\epsilon}:$$
--   a partition into clusters of strong diameter at most $\epsilon\operatorname{diam}(G)$ such that for all $u,v$ and every shortest $u$–$v$ path $Q$ there is a path in $G/\mathcal C$ from the cluster of $u$ to that of $v$ with at most $\epsilon h\lceil d_G(u,v)/(\epsilon\operatorname{diam}(G))\rceil$ hops, through clusters meeting $Q$ only.
--
--   This is the shortcut partition theorem of Chang, Conroy, Le, Milenković, Solomon and Than (2024), which the proof of Theorem 2 uses to pass from unweighted to weighted graphs.
--
--   Differences from the source:
--   - reading: 2^{O(r log r)} → one explicit existentially quantified universal constant, chosen before every other quantity; reason: p. 13: O(·) has universal hidden constants unless otherwise stated
--   - encoding: graph (with the standing assumption 'we will assume all input graphs are connected', p. 14) → hypothesis `Connected G` (d_G(u, v) < ∞ for all u, v); reason: standing assumption of §3.1 made explicit
--   - reading: 'π only contains a subset of clusters that have nontrivial intersections with a given shortest path in G between u and v' → for every shortest u–v path Q there is such a path through clusters meeting Q; reason: 'a given' shortest path is read as an arbitrary one fixed in advance, the stronger of the two readings
--   - generalization: edge-weighted graph (with the standing convention w(e) ∈ [1, poly(n)], p. 13) → arbitrary positive weights; reason: the cited theorem is stated for any edge-weighted graph; bounded aspect ratio is a special case
--   - encoding: distances d_G, d_C, d_T and α·d_G(u, v) → values in [0, ∞] (`ℝ≥0∞`), α·d as `ENNReal.ofReal α * d`; reason: the published `WGraph.dist`/`distIn` convention; on connected graphs and connected clusters every distance is finite
-- source:
--   Filtser, Fletcher, Hershkowitz, Milenković, (1 + ϵ)-Distortion Spanning Tree Covers of Minor-Free Graphs with Size O(log log n), STOC 2027 submission (manuscript sha256 f475e254…), p. 18, Theorem 7

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_MinorFreeSTC_Main_Graphs
import Definitions.Def_MinorFreeSTC_Main_Structures

set_option autoImplicit false

open scoped ENNReal

namespace MinorFreeSTC.Main

open ARTreeCover

/-- **Theorem 7** ([CCL+24], p. 18). There is a universal `c` such that every connected
edge-weighted `K_r`-minor-free graph admits an `(ϵ, 2^{c r log r}/ϵ)`-shortcut partition for every
`ϵ ∈ (0, 1)`. -/
theorem theorem_7 :
    ∃ c : ℝ, 0 < c ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : WGraph V) (r : ℕ) (ϵ : ℝ),
        Connected G → MinorFree G r → 0 < ϵ → ϵ < 1 →
        ∃ 𝒞 : Finset (Finset V),
          IsShortcutPartition G 𝒞 ϵ ((2 : ℝ) ^ (c * r * Real.logb 2 r) / ϵ) := by sorry

end MinorFreeSTC.Main

-- Prove2me | Theorems.Thm_MinorFreeSTC_Main_theorem_6
-- name    : MinorFreeSTC.Main.theorem_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:18:24.244254+00:00
-- url     : https://prove2.me/theorems/4781f626-f2d3-47d5-850d-4977c56b8d84
-- title:
--   Theorem 6 — K_r-minor-free graphs have a total order with |WReach_2(u)| ≤ 5·binom(r,2)·(r−3) ([HMQ+17, Thm 1.4])
-- statement:
--   Let $r\ge4$ and let $G$ be a finite simple graph with no $K_r$ minor. Then there is a total order $\pi$ on $V(G)$ such that for every vertex $u$
--   $$|\mathrm{WReach}^\pi_2(u)|\ \le\ 5\binom r2(r-3)=\kappa_r,$$
--   where $\mathrm{WReach}^\pi_2(u)$ is the set of vertices $x$ reachable from $u$ by a path of at most two edges on which $x$ is the $\pi$-minimum.
--
--   This is Theorem 1.4 of van den Heuvel, Ossona de Mendez, Quiroz, Rabinovich and Siebertz (2017), the bound on the weak 2-colouring number of $K_r$-minor-free graphs; Lemma 2 uses it to build a forest whose sparse partitions transfer to the graph.
--
--   **Formalization Note.** A total order is an injective rank $\pi:V\to\mathbb N$.
--
--   Differences from the source:
--   - encoding: total order π on the vertices → injective rank π : V → ℕ (u precedes v iff π u < π v); reason: every total order on a finite set is induced by such a rank
--   - generalization: graph G (with the standing assumption that input graphs are connected, p. 14) → every finite simple graph, connected or not; reason: the theorem is stated 'for every graph G' and cited from [HMQ+17]; connected graphs are a special case
-- source:
--   Filtser, Fletcher, Hershkowitz, Milenković, (1 + ϵ)-Distortion Spanning Tree Covers of Minor-Free Graphs with Size O(log log n), STOC 2027 submission (manuscript sha256 f475e254…), p. 17, Theorem 6

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_HadwigerConj_Defs
import Definitions.Def_MinorFreeSTC_Main_Graphs
import Definitions.Def_MinorFreeSTC_Main_Structures

set_option autoImplicit false

open scoped ENNReal

namespace MinorFreeSTC.Main

open ARTreeCover

/-- **Theorem 6** (Theorem 1.4 in [HMQ+17], p. 17). Let `r ≥ 4`. Every finite graph without a
`K_r` minor has a total order `π` with `|WReach^π_2(u)| ≤ 5 · binom(r, 2) · (r − 3)` for every
vertex `u`. -/
theorem theorem_6 (r : ℕ) (hr : 4 ≤ r) (V : Type) [Fintype V] (G : SimpleGraph V)
    (hG : ¬ HadwigerConj.HasCompleteMinor G r) :
    ∃ π : V → ℕ, Function.Injective π ∧
      ∀ u : V, (WReach2 G π u).ncard ≤ 5 * Nat.choose r 2 * (r - 3) := by sorry

end MinorFreeSTC.Main

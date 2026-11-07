-- Prove2me | Theorems.Thm_MulticastPoS_optimum_tree
-- name    : MulticastPoS.optimum_tree
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:40:43.295792+00:00
-- url     : https://prove2.me/theorems/e1fb40c3-d00d-4b60-a215-f641fc21c5bb
-- title:
--   Section 1 — an optimum can be chosen as a minimum-cost tree connecting all sources to $t$
-- statement:
--   Let the edge costs be nonnegative.
--
--   1. For every path profile $Q$ there is a tree $S\subseteq\operatorname{supp}(Q)$ containing $t$ and every source with $c(S)\le SC(Q)$.
--   2. Conversely, for every tree $S\subseteq G$ containing $t$ and every source, the tree paths $S[s_i,t]$ form a path profile $Q$ with $\operatorname{supp}(Q)\subseteq E(S)$ and $SC(Q)\le c(S)$.
--
--   Together, the least social cost of a profile equals the least cost $OPT=c(T^\star)$ of a tree connecting all sources to $t$, which is the benchmark of the price of stability.
--
--   Differences from the source:
--   - encoding: finite undirected graph G = (V, E); player i chooses a simple path P_i from s_i to t; n players → SimpleGraph on a Fintype V; strategies are the edge sets p.edges.toFinset of walks p : G.Walk (s i) t with p.IsPath; players a Fintype ι; reason: the same games: loops never lie on a simple path, a parallel edge is equivalent to a subdivided edge with costs c_e and 0 (same strategies, payments, potential and social cost), and payments, loads, Φ and SC depend on a path only through its edge set
--   - encoding: a nonnegative cost c_e on each edge e → c : Sym2 V → ℝ with 0 ≤ c e for every e ∈ G.edgeSet; reason: the values of c off the graph never enter: no strategy contains a non-edge
--   - reading: the used edges of an optimum connect every source to t; since edge costs are nonnegative, an optimum can be chosen as a minimum-cost tree connecting all sources to t → two clauses: every profile's support contains such a tree of no larger cost, and every such tree carries a profile of no larger social cost; reason: together they say exactly that the minimum of SC over profiles is attained by (the paths of) a cheapest tree connecting all sources to t
-- source:
--   Huang–Yuan, An O(log log n) Upper Bound on the Price of Stability for Undirected Multicast Shapley Games, STOC 2027 submission (manuscript sha256 dd0e08d0…), Section 1, p.1 (PDF p.2)

import Mathlib
import Definitions.Def_MulticastPoS_game
import Definitions.Def_MulticastPoS_socialCost
import Definitions.Def_MulticastPoS_subgraphCost
import Definitions.Def_MulticastPoS_IsTerminalTree

open CongestionPoA.AsymSum PriceOfStability.Harmonic

namespace MulticastPoS

/-- An optimum can be chosen as a tree (Huang–Yuan, *An O(log log n) Upper Bound on the Price of
Stability for Undirected Multicast Shapley Games*, STOC 2027 submission manuscript (sha256
dd0e08d0…f6d4), Section 1, p.1): the used edges of a path profile connect every source to `t`,
and since edge costs are nonnegative, an optimum can be chosen as a minimum-cost tree
connecting all sources to `t`. Precisely:

1. for every profile `Q` there is a tree `S` through `t` and all sources, using only edges of
   `supp(Q)`, with `c(S) ≤ SC(Q)`;
2. conversely, for every tree `S` through `t` and all sources, the tree paths form a profile `Q`
   with `supp(Q) ⊆ E(S)` and `SC(Q) ≤ c(S)`.

So the minimum of `SC` over profiles equals the cost `OPT` of a cheapest such tree. -/
theorem optimum_tree {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph V) (c : Sym2 V → ℝ) (t : V) (s : ι → V)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) :
    (∀ Q : ι → Finset (Sym2 V), IsProfile (game G c t s) Q →
      ∃ S : G.Subgraph, IsTerminalTree G t s S ∧
        S.edgeSet ⊆ ↑(Finset.univ.biUnion Q) ∧ subgraphCost c S ≤ socialCost c Q) ∧
    (∀ S : G.Subgraph, IsTerminalTree G t s S →
      ∃ Q : ι → Finset (Sym2 V), IsProfile (game G c t s) Q ∧
        ↑(Finset.univ.biUnion Q) ⊆ S.edgeSet ∧ socialCost c Q ≤ subgraphCost c S) := by sorry

end MulticastPoS

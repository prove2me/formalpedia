-- Prove2me | Theorems.Thm_MulticastPoS_lemma_4_1
-- name    : MulticastPoS.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:40:50.543938+00:00
-- url     : https://prove2.me/theorems/1ffde25e-b129-40b3-a3db-ac616e916273
-- title:
--   Lemma 4.1 — groups with edge-disjoint connected subgraphs
-- statement:
--   Let $Q\ge 1$ be an integer and $S\subseteq G$ a tree containing $t$ and every source. The source occurrences on $S$ can be partitioned into groups with associated subgraphs $(R_g)$ such that every nonresidual group has $Q\le|g|<2Q$; there is at most one residual group $g_0$, with $|g_0|<Q$ and $t\in V(R_{g_0})$; each $R_g$ is a connected subgraph of $S$ with
--
--   $$
--   \ell(g)\subseteq V(R_g),\qquad E(R_g)\cap E(R_h)=\emptyset\quad(g\ne h).
--   $$
--
--   Consequently, for nonnegative edge costs, $\sum_{g} c(R_g)\le c(S)$.
--
--   Applied to $S=T^\star$, the subgraphs have total cost at most $OPT$; the random profile of Lemma 3.2 routes each group inside its subgraph.
--
--   Differences from the source:
--   - encoding: finite undirected graph G = (V, E); player i chooses a simple path P_i from s_i to t; n players → SimpleGraph on a Fintype V; strategies are the edge sets p.edges.toFinset of walks p : G.Walk (s i) t with p.IsPath; players a Fintype ι; reason: the same games: loops never lie on a simple path, a parallel edge is equivalent to a subdivided edge with costs c_e and 0 (same strategies, payments, potential and social cost), and payments, loads, Φ and SC depend on a path only through its edge set
--   - encoding: a nonnegative cost c_e on each edge e → c : Sym2 V → ℝ with 0 ≤ c e for every e ∈ G.edgeSet; reason: the values of c off the graph never enter: no strategy contains a non-edge
--   - encoding: source occurrences o_i with locations ℓ(o_i) = s_i, groups of occurrences → players i ∈ ι with sources s i, groups as Finsets of players; reason: occurrences are in bijection with players (p.4)
--   - reading: 'The procedure partitions the source occurrences on S into groups …' (the leaves-to-root procedure of Section 4.1, whose item-merging order is left free) → there exist a partition π, an optional residual group g₀ and subgraphs R satisfying every listed guarantee (IsGrouping) and the cost bound; reason: the procedure is nondeterministic in its merge order and every run has these properties; Sections 4.2–5 use only these properties
-- source:
--   Huang–Yuan, An O(log log n) Upper Bound on the Price of Stability for Undirected Multicast Shapley Games, STOC 2027 submission (manuscript sha256 dd0e08d0…), Lemma 4.1, p.8 (PDF p.9); procedure Section 4.1, pp.7–8; proof Appendix B, pp.14–15

import Mathlib
import Definitions.Def_MulticastPoS_subgraphCost
import Definitions.Def_MulticastPoS_IsTerminalTree
import Definitions.Def_MulticastPoS_IsGrouping

namespace MulticastPoS

/-- Lemma 4.1, groups with edge-disjoint connected subgraphs (Huang–Yuan, *An O(log log n) Upper
Bound on the Price of Stability for Undirected Multicast Shapley Games*, STOC 2027 submission
manuscript (sha256 dd0e08d0…f6d4), p.8; procedure pp.7–8, proof in Appendix B, pp.14–15): for
every integer `Q ≥ 1` and every finite tree `S ⊆ G` containing `t` and the source locations,
the grouping procedure partitions the source occurrences into groups such that every
nonresidual group has `Q ≤ |g| < 2Q`, there is at most one residual group `g₀`, with
`|g₀| < Q` and `t ∈ V(R_{g₀})`, each `R_g` is a connected subgraph of `S` with
`ℓ(g) ⊆ V(R_g)`, and `E(R_g) ∩ E(R_h) = ∅` for `g ≠ h`; consequently, for nonnegative costs,
`Σ_{g} c(R_g) ≤ c(S)`.

**Formalization Note** The procedure leaves the order in which items are merged free (p.7), so
the lemma is stated as the existence of a grouping with all the guarantees the lemma lists
(`IsGrouping`). Source occurrences are the players. -/
theorem lemma_4_1 {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph V) (c : Sym2 V → ℝ) (t : V) (s : ι → V)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (Q : ℕ) (hQ : 1 ≤ Q) (S : G.Subgraph)
    (hS : IsTerminalTree G t s S) :
    ∃ (π : Finpartition (Finset.univ : Finset ι)) (g₀ : Option (Finset ι))
      (R : Finset ι → G.Subgraph),
      IsGrouping t s Q S π g₀ R ∧ ∑ g ∈ π.parts, subgraphCost c (R g) ≤ subgraphCost c S := by sorry

end MulticastPoS

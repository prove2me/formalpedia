-- Prove2me | Theorems.Thm_MulticastPoS_lemma_5_2
-- name    : MulticastPoS.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:40:47.073526+00:00
-- url     : https://prove2.me/theorems/0def2381-773d-485d-b753-31649c1d3acd
-- title:
--   Lemma 5.2 — contribution of the local segments: $\sum_f c_fH_{A_f}\le H_{8K}\,OPT$
-- statement:
--   Let the edge costs be nonnegative, let $K\ge 4$ be an integer, and let $S$ be a tree containing $t$ and every source. Take a grouping with parameter $Q=4K$ on $S$ (Lemma 4.1), and suppose every player's local segment $L_i$ runs inside the subgraph $R_g$ of its group $g$. Then
--
--   $$
--   \sum_{f} c_f H_{A_f}\le H_{8K}\,c(S), \tag{10}
--   $$
--
--   where $A_f$ is the number of local segments using $f$. For $S=T^\star$ the right side is $H_{8K}\,OPT$.
--
--   The bound holds for every representative selection; no averaging is needed for the local segments.
--
--   Differences from the source:
--   - encoding: finite undirected graph G = (V, E); player i chooses a simple path P_i from s_i to t; n players → SimpleGraph on a Fintype V; strategies are the edge sets p.edges.toFinset of walks p : G.Walk (s i) t with p.IsPath; players a Fintype ι; reason: the same games: loops never lie on a simple path, a parallel edge is equivalent to a subdivided edge with costs c_e and 0 (same strategies, payments, potential and social cost), and payments, loads, Φ and SC depend on a path only through its edge set
--   - encoding: a nonnegative cost c_e on each edge e → c : Sym2 V → ℝ with 0 ≤ c e for every e ∈ G.edgeSet; reason: the values of c off the graph never enter: no strategy contains a non-edge
--   - generalization: the optimal tree T⋆ and OPT = c(T⋆) → any subgraph S of G that is a tree containing t and every source, and its cost c(S); reason: T⋆ is such a tree, so taking S = T⋆ gives the source's statement
--   - generalization: the groups and subgraphs produced by the procedure of Section 4.1 with Q = 4K on T⋆ → any partition π of the players, optional residual group g₀ and subgraphs R with IsGrouping t s (4K) S π g₀ R; reason: Lemma 4.1 shows the procedure's output satisfies IsGrouping; the statement holds for every grouping with those guarantees
--   - generalization: the local segments of a representative selection (walks inside R_g from s_i to the representative's source, or to t for the residual group) → any walks L_i : s_i → m_i whose edges all lie in R_g for the group g ∋ i; reason: the local segments of every selection are such walks
-- source:
--   Huang–Yuan, An O(log log n) Upper Bound on the Price of Stability for Undirected Multicast Shapley Games, STOC 2027 submission (manuscript sha256 dd0e08d0…), Lemma 5.2, p.10 (PDF p.11), Eq. (10)

import Mathlib
import Definitions.Def_MulticastPoS_subgraphCost
import Definitions.Def_MulticastPoS_IsTerminalTree
import Definitions.Def_MulticastPoS_IsGrouping
import Definitions.Def_MulticastPoS_walkCount

namespace MulticastPoS

/-- Lemma 5.2, contribution of the local segments (Huang–Yuan, *An O(log log n) Upper Bound on
the Price of Stability for Undirected Multicast Shapley Games*, STOC 2027 submission manuscript
(sha256 dd0e08d0…f6d4), p.10): for an integer `K ≥ 4`, take the groups of Lemma 4.1 with
`Q = 4K` on a tree `S` through `t` and all sources. If every player's local segment `Lᵢ` stays
inside the subgraph `R_g` of its group, then, for nonnegative costs,
`Σ_f c_f H_{A_f} ≤ H_{8K} c(S)`, where `A_f` is the number of local segments using `f`.

**Formalization Note** The paper states this for `S = T⋆` (so `c(S) = OPT`) and the local
segments of every representative selection; the statement covers every tree `S` through `t` and
all sources and every family of walks inside the groups' subgraphs. -/
theorem lemma_5_2 {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph V) (c : Sym2 V → ℝ) (t : V) (s : ι → V)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (K : ℕ) (hK : 4 ≤ K) (S : G.Subgraph)
    (hS : IsTerminalTree G t s S) (π : Finpartition (Finset.univ : Finset ι))
    (g₀ : Option (Finset ι)) (R : Finset ι → G.Subgraph)
    (hgr : IsGrouping t s (4 * K) S π g₀ R) (m : ι → V) (L : ∀ i, G.Walk (s i) (m i))
    (hL : ∀ g ∈ π.parts, ∀ i ∈ g, ∀ f ∈ (L i).edges, f ∈ (R g).edgeSet) :
    (∑ f, c f * (harmonic (walkCount L f) : ℝ)) ≤
      (harmonic (8 * K) : ℝ) * subgraphCost c S := by sorry

end MulticastPoS

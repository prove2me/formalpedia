-- Prove2me | Theorems.Thm_MulticastPoS_lemma_3_2
-- name    : MulticastPoS.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:41:04.319353+00:00
-- url     : https://prove2.me/theorems/42bfb428-e2c7-460b-a0d9-8150cfc52596
-- title:
--   Lemma 3.2 — the expected potential of the new profile
-- statement:
--   Let the edge costs be nonnegative, let $P$ be a path profile with loads $x_e$ and $T=\operatorname{supp}(P)$, and let $T^\star$ be a tree containing $t$ and every source with $c(T^\star)=OPT$. For every integer $K\ge 4$ there is a random feasible path profile $P^{(K)}$ satisfying
--
--   $$
--   \mathbb E\,\Phi(P^{(K)})\le\Phi(P)-\frac12\sum_{e\in T:\,1\le x_e<K}c_eH_{x_e}+H_{8K}\,OPT. \tag{8}
--   $$
--
--   Combined with the global minimality of $P$, this proves Lemma 3.1.
--
--   **Formalization Note** The random profile is a nonempty finite multiset of feasible profiles drawn uniformly, and $\mathbb E\,\Phi$ is the average of $\Phi$ over it.
--
--   Differences from the source:
--   - encoding: finite undirected graph G = (V, E); player i chooses a simple path P_i from s_i to t; n players → SimpleGraph on a Fintype V; strategies are the edge sets p.edges.toFinset of walks p : G.Walk (s i) t with p.IsPath; players a Fintype ι; reason: the same games: loops never lie on a simple path, a parallel edge is equivalent to a subdivided edge with costs c_e and 0 (same strategies, payments, potential and social cost), and payments, loads, Φ and SC depend on a path only through its edge set
--   - encoding: a nonnegative cost c_e on each edge e → c : Sym2 V → ℝ with 0 ≤ c e for every e ∈ G.edgeSet; reason: the values of c off the graph never enter: no strategy contains a non-edge
--   - generalization: P the fixed tree-supported global potential minimizer → any path profile P; reason: the construction and the proof (Lemmas 5.1–5.3, Corollary 5.5) use only that P is a path profile
--   - generalization: the optimal tree T⋆ and OPT = c(T⋆) → any subgraph S of G that is a tree containing t and every source, and its cost c(S); reason: T⋆ is such a tree, so taking S = T⋆ gives the source's statement
--   - encoding: a random feasible path profile P^(K) → a nonempty multiset M of feasible profiles, with E Φ the average of Φ over M; reason: a uniform draw from M is a random feasible profile, and the paper's P^(K), uniform over the finitely many representative selections, is of this form
-- source:
--   Huang–Yuan, An O(log log n) Upper Bound on the Price of Stability for Undirected Multicast Shapley Games, STOC 2027 submission (manuscript sha256 dd0e08d0…), Lemma 3.2, p.6 (PDF p.7), Eq. (8); construction Section 4, proof Section 5

import Mathlib
import Definitions.Def_MulticastPoS_game
import Definitions.Def_MulticastPoS_subgraphCost
import Definitions.Def_MulticastPoS_IsTerminalTree

open CongestionPoA.AsymSum PriceOfStability.Harmonic

namespace MulticastPoS

/-- Lemma 3.2, the expected potential of the new profile (Huang–Yuan, *An O(log log n) Upper
Bound on the Price of Stability for Undirected Multicast Shapley Games*, STOC 2027 submission
manuscript (sha256 dd0e08d0…f6d4), p.6, Eq. (8); construction Section 4, proof Section 5): for
every integer `K ≥ 4` there is a random feasible path profile `P^(K)` with
`E Φ(P^(K)) ≤ Φ(P) − ½ Σ_{e ∈ T : 1 ≤ x_e < K} c_e H_{x_e} + H_{8K} OPT`.

**Formalization Note** The random profile is a nonempty multiset `M` of feasible profiles,
drawn uniformly (the paper's `P^(K)` is uniform over representative selections, which gives such
a multiset); `E Φ` is the average of `Φ` over `M`. `e ∈ T` with `1 ≤ x_e` is `1 ≤ x_e`. The paper
fixes `P` the tree-supported global minimizer and `OPT = c(T⋆)`; the statement covers every path
profile `P` and every tree `S` through `t` and all sources, with `c(S)` for `OPT`. -/
theorem lemma_3_2 {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph V) (c : Sym2 V → ℝ) (t : V) (s : ι → V)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (P : ι → Finset (Sym2 V))
    (hP : IsProfile (game G c t s) P) (S : G.Subgraph) (hS : IsTerminalTree G t s S)
    (K : ℕ) (hK : 4 ≤ K) :
    ∃ M : Multiset (ι → Finset (Sym2 V)), M ≠ 0 ∧ (∀ R ∈ M, IsProfile (game G c t s) R) ∧
      (M.map (potential (game G c t s))).sum / M.card ≤
        potential (game G c t s) P -
          (1 / 2) * (∑ e ∈ Finset.univ.filter (fun e => 1 ≤ load P e ∧ load P e < K),
            c e * (harmonic (load P e) : ℝ)) +
          (harmonic (8 * K) : ℝ) * subgraphCost c S := by sorry

end MulticastPoS

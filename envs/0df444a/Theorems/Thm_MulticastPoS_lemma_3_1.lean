-- Prove2me | Theorems.Thm_MulticastPoS_lemma_3_1
-- name    : MulticastPoS.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:41:14.1297+00:00
-- url     : https://prove2.me/theorems/a3da6211-c6b6-440c-bf55-76b3a19c17ea
-- title:
--   Lemma 3.1 with Eq. (6) — total potential below a load threshold: $\sum_{1\le x_e<K}c_eH_{x_e}\le 2H_{8K}\,OPT$
-- statement:
--   Let the edge costs be nonnegative and let $P$ be a global minimizer of the potential, with loads $x_e$ and $T=\operatorname{supp}(P)$. For every integer $K\ge 4$:
--
--   1. (5) For every tree $S$ containing $t$ and every source, and for every path profile $Q$,
--   $$
--   \sum_{e\in T:\,1\le x_e<K}c_eH_{x_e}\le 2H_{8K}\,c(S)\quad\text{and}\quad\sum_{e\in T:\,1\le x_e<K}c_eH_{x_e}\le 2H_{8K}\,SC(Q);
--   $$
--   in particular the sum is at most $2H_{8K}\,OPT$.
--   2. (6) For every integer $1\le L<K$, with $B[L,K)=\sum_{e\in T:\,L\le x_e<K}c_e$,
--   $$
--   H_L\,B[L,K)\le\sum_{e\in T:\,1\le x_e<K}c_eH_{x_e}\ (\le 2H_{8K}\,OPT).
--   $$
--
--   Dividing by $H_L$ bounds the cost of the load range $[L,K)$ by $(2H_{8K}/H_L)\,OPT$, the range bound of Table 1.
--
--   Differences from the source:
--   - encoding: finite undirected graph G = (V, E); player i chooses a simple path P_i from s_i to t; n players → SimpleGraph on a Fintype V; strategies are the edge sets p.edges.toFinset of walks p : G.Walk (s i) t with p.IsPath; players a Fintype ι; reason: the same games: loops never lie on a simple path, a parallel edge is equivalent to a subdivided edge with costs c_e and 0 (same strategies, payments, potential and social cost), and payments, loads, Φ and SC depend on a path only through its edge set
--   - encoding: a nonnegative cost c_e on each edge e → c : Sym2 V → ℝ with 0 ≤ c e for every e ∈ G.edgeSet; reason: the values of c off the graph never enter: no strategy contains a non-edge
--   - encoding: standing assumption: a path from each source to t exists (p.1) → not a separate hypothesis; reason: it is implied by the hypothesis that a (global-minimizer) profile exists, since every player then has an s_i–t path
--   - generalization: P the fixed tree-supported global potential minimizer → any global minimizer P; reason: the proof (via Lemma 3.2) uses only the global minimality of P
--   - encoding: OPT = c(T⋆) → the bound against c(S) for every tree S through t and all sources, and against SC(Q) for every path profile Q; reason: OPT is the least such c(S) and the least such SC(Q) (optimum-as-tree milestone)
--   - encoding: e ∈ T with 1 ≤ x_e (resp. L ≤ x_e) → the load condition alone; reason: T = supp(P) is the set of edges with positive load
-- source:
--   Huang–Yuan, An O(log log n) Upper Bound on the Price of Stability for Undirected Multicast Shapley Games, STOC 2027 submission (manuscript sha256 dd0e08d0…), Lemma 3.1 and Eq. (6), p.5 (PDF p.6)

import Mathlib
import Definitions.Def_MulticastPoS_game
import Definitions.Def_MulticastPoS_socialCost
import Definitions.Def_MulticastPoS_subgraphCost
import Definitions.Def_MulticastPoS_IsTerminalTree
import Definitions.Def_MulticastPoS_IsGlobalMin

open CongestionPoA.AsymSum PriceOfStability.Harmonic

namespace MulticastPoS

/-- Lemma 3.1, total potential below a load threshold, with Eq. (6) (Huang–Yuan, *An
O(log log n) Upper Bound on the Price of Stability for Undirected Multicast Shapley Games*,
STOC 2027 submission manuscript (sha256 dd0e08d0…f6d4), p.5): for a global minimizer `P` of the
potential and every integer `K ≥ 4`,

1. (5) `Σ_{e ∈ T : 1 ≤ x_e < K} c_e H_{x_e} ≤ 2 H_{8K} OPT`, with `OPT` read both as the cost of
   any tree through `t` and all sources and as the social cost of any profile;
2. (6) for every integer `1 ≤ L < K`,
   `H_L B[L, K) ≤ Σ_{e ∈ T : 1 ≤ x_e < K} c_e H_{x_e} ≤ 2 H_{8K} OPT`, where
   `B[L, K) = Σ_{e ∈ T : L ≤ x_e < K} c_e`.

**Formalization Note** `T = supp(P)`, so `e ∈ T` with `1 ≤ x_e` (or `L ≤ x_e`, `L ≥ 1`) is just
the load condition. `OPT` is not a variable: it is bounded through every tree `S` through `t`
and all sources and every profile `Q`. The paper takes `P` tree-supported; the statement covers
every global minimizer. -/
theorem lemma_3_1 {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph V) (c : Sym2 V → ℝ) (t : V) (s : ι → V)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (P : ι → Finset (Sym2 V))
    (hP : IsGlobalMin (game G c t s) P) (K : ℕ) (hK : 4 ≤ K) :
    (∀ S : G.Subgraph, IsTerminalTree G t s S →
      (∑ e ∈ Finset.univ.filter (fun e => 1 ≤ load P e ∧ load P e < K),
          c e * (harmonic (load P e) : ℝ)) ≤
        2 * (harmonic (8 * K) : ℝ) * subgraphCost c S) ∧
    (∀ Q, IsProfile (game G c t s) Q →
      (∑ e ∈ Finset.univ.filter (fun e => 1 ≤ load P e ∧ load P e < K),
          c e * (harmonic (load P e) : ℝ)) ≤
        2 * (harmonic (8 * K) : ℝ) * socialCost c Q) ∧
    (∀ L : ℕ, 1 ≤ L → L < K →
      (harmonic L : ℝ) * (∑ e ∈ Finset.univ.filter (fun e => L ≤ load P e ∧ load P e < K), c e) ≤
        ∑ e ∈ Finset.univ.filter (fun e => 1 ≤ load P e ∧ load P e < K),
          c e * (harmonic (load P e) : ℝ)) := by sorry

end MulticastPoS

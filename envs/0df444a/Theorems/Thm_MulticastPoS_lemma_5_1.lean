-- Prove2me | Theorems.Thm_MulticastPoS_lemma_5_1
-- name    : MulticastPoS.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:39:59.571491+00:00
-- url     : https://prove2.me/theorems/de8db604-1ca0-4dab-b799-b9f7aafeef67
-- title:
--   Lemma 5.1 — feasibility and edge counts
-- statement:
--   Let every player $i$ have a raw walk $W_i=L_iD_i$: a walk $L_i$ from $s_i$ to a vertex $m_i$ followed by a walk $D_i$ from $m_i$ to $t$. For an edge $f$ write $A_f=\sum_i\mathbf 1[f\in L_i]$ and $D_f=\sum_i\mathbf 1[f\in D_i]$.
--
--   1. Loop erasure is feasible: there is a path profile $R$ (each $R_i$ the edge set of a simple $s_i$–$t$ path) that uses only edges of the raw walks.
--   2. Every profile $R$ that uses only edges of the raw walks satisfies
--
--   $$
--   x_f(R)\le A_f+D_f\quad\text{for every edge } f.
--   $$
--
--   In the paper, $L_i$ is player $i$'s local segment, $D_i$ its copied tail, and $R=P^{(K)}$ is the loop-erased profile; the lemma reduces the potential of $P^{(K)}$ to the two counts.
--
--   Differences from the source:
--   - encoding: finite undirected graph G = (V, E); player i chooses a simple path P_i from s_i to t; n players → SimpleGraph on a Fintype V; strategies are the edge sets p.edges.toFinset of walks p : G.Walk (s i) t with p.IsPath; players a Fintype ι; reason: the same games: loops never lie on a simple path, a parallel edge is equivalent to a subdivided edge with costs c_e and 0 (same strategies, payments, potential and social cost), and payments, loads, Φ and SC depend on a path only through its edge set
--   - generalization: for every representative selection, the profile P^(K) obtained by the fixed loop-erasure rule of Appendix C from local segments followed by the representative's path → for every family of walks L_i : s_i → m_i, D_i : m_i → t: existence of a path profile inside the raw walks, and the load bound for every profile inside the raw walks; reason: the paper's walks are such a family and its loop-erasure output only deletes traversals, so it is a profile inside the raw walks
-- source:
--   Huang–Yuan, An O(log log n) Upper Bound on the Price of Stability for Undirected Multicast Shapley Games, STOC 2027 submission (manuscript sha256 dd0e08d0…), Lemma 5.1, p.9 (PDF p.10); loop-erasure rule and proof Appendix C, p.15

import Mathlib
import Definitions.Def_MulticastPoS_pathStrategies
import Definitions.Def_MulticastPoS_walkCount
import Definitions.Def_CongestionPoA_AsymSum_Model

open CongestionPoA.AsymSum

namespace MulticastPoS

/-- Lemma 5.1, feasibility and edge counts (Huang–Yuan, *An O(log log n) Upper Bound on the Price
of Stability for Undirected Multicast Shapley Games*, STOC 2027 submission manuscript (sha256
dd0e08d0…f6d4), p.9; proof in Appendix C, p.15): let each player `i` have a raw walk
`Wᵢ = Lᵢ Dᵢ`, a walk `Lᵢ` from `sᵢ` to some vertex `mᵢ` followed by a walk `Dᵢ` from `mᵢ` to
`t`. Then

1. loop erasure is feasible: there is a path profile `R` (every `Rᵢ` the edge set of a simple
   `sᵢ`–`t` path) using only edges of the raw walks;
2. every profile `R` that uses only edges of the raw walks satisfies
   `x_f(R) ≤ A_f + D_f` for every edge `f`, where `A_f = Σᵢ 1[f ∈ Lᵢ]` and
   `D_f = Σᵢ 1[f ∈ Dᵢ]`.

**Formalization Note** In the paper `Lᵢ` is the local segment and `Dᵢ` the copied tail (the
representative's path, empty for the residual group), and `P^(K)` is obtained by one fixed
loop-erasure rule; the lemma is stated for every family of walks and every loop-erasure output
that only deletes traversals. -/
theorem lemma_5_1 {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph V) (t : V) (s m : ι → V)
    (L : ∀ i, G.Walk (s i) (m i)) (D : ∀ i, G.Walk (m i) t) :
    (∃ R : ι → Finset (Sym2 V), (∀ i, R i ∈ pathStrategies G t s i) ∧
      ∀ i, R i ⊆ ((L i).edges ++ (D i).edges).toFinset) ∧
    (∀ R : ι → Finset (Sym2 V), (∀ i, R i ⊆ ((L i).edges ++ (D i).edges).toFinset) →
      ∀ f, load R f ≤ walkCount L f + walkCount D f) := by sorry

end MulticastPoS

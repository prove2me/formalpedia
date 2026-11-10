-- Prove2me | Theorems.Thm_MultiAllocToAlloc_Subadditive_theorem_13
-- name    : MultiAllocToAlloc.Subadditive.theorem_13
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T18:10:42.772577+00:00
-- url     : https://prove2.me/theorems/985c599e-b833-4930-8776-35ff01a786f5
-- title:
--   Theorem 13 — in a multigraph instance some orientation gives every agent i at least ω(S_q, M_i, v_i)
-- statement:
--   Let $G$ be a multigraph whose $n$ vertices are the agents and whose $m$ edges are the items (parallel edges allowed, no loops); $M_i$ is the set of edges incident with agent $i$. Every agent $i$ has a valuation $v_i$ on sets of items that is normalized ($v_i(\emptyset)=0$) and monotone, and depends only on the items incident with $i$: $v_i(T)=v_i(T\cap M_i)$ for every $T$ (all other items have $0$ marginal value). An allocation is an orientation: each edge is given to one of its two endpoints. Here, for a valuation v and a finite item set M, ω(S_p, M, v) and ω(S_q, M, v) (Definition 7, p. 6) are the maximin values that a player p with valuation v (her payoff is v(T) for the set T of items she picks; the opponent q's payoff is −v(T)) can guarantee in the picking game on the finite item set M with the alternating picking sequence of length |M| that starts with p (S_p) or with q (S_q); every item of M is picked. Then there is an orientation $o$ in which every agent $i$ receives a bundle $B_i=\{e : o(e)=i\}$ with
--   $$v_i(B_i)\ \ge\ \omega(S_q,M_i,v_i).$$
--
--   Differences from the source:
--   - encoding: a multigraph G on the agents (parallel edges allowed) whose edges are the items; each agent has a valuation over M_i and 0 marginal value for every other item; allocations are orientations → Multigraph n m (edges Fin m with two distinct endpoints in Fin n), v : Fin n → Finset (Fin m) → ℝ with v i T = v i (T ∩ M_i) for all T (IsMultigraphInstance), and an orientation o : Fin m → Fin n with o e an endpoint of e, agent i receiving bundleOf o i = {e | o e = i}; reason: a direct transcription of §2.2; an edge joins two agents, so loops are not part of the model, and 0 marginal value outside M_i is exactly v_i(T) = v_i(T ∩ M_i)
-- source:
--   Feige, arXiv:2506.21493v1, Theorem 13, p. 9

import Mathlib
import Definitions.Def_MultiAllocToAlloc_Subadditive_Valuation
import Definitions.Def_MultiAllocToAlloc_Subadditive_PickingGame
import Definitions.Def_MultiAllocToAlloc_Subadditive_Multigraph

namespace MultiAllocToAlloc.Subadditive

/-- Feige, arXiv:2506.21493v1, Theorem 13, p. 9: in a multigraph allocation instance with
normalized monotone valuations there is an orientation (allocation) in which every agent `i`
receives a bundle of value at least `ω(S_q, M_i, v_i)`. -/
theorem theorem_13 {n m : ℕ} (G : Multigraph n m) (v : Fin n → Finset (Fin m) → ℝ)
    (hnorm : ∀ i, IsNormalized (v i)) (hmono : ∀ i, IsMonotone (v i))
    (hG : IsMultigraphInstance G v) :
    ∃ o : Fin m → Fin n, G.IsOrientation o ∧
      ∀ i : Fin n, omegaQ (v i) (G.incident i) ≤ v i (bundleOf o i) := by sorry

end MultiAllocToAlloc.Subadditive

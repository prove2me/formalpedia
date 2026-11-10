-- Prove2me | Theorems.Thm_MultiAllocToAlloc_Subadditive_corollary_14
-- name    : MultiAllocToAlloc.Subadditive.corollary_14
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T18:10:27.941803+00:00
-- url     : https://prove2.me/theorems/a471606f-0e88-479f-8ce3-6d60cebfb446
-- title:
--   Corollary 14 — multigraph instances with subadditive valuations: an orientation giving every i at least (v_i(M) − δ_i)/2 and at least ½·MMS(M, v_i, 2) ≥ ½·MMS(M, v_i, n)
-- statement:
--   Let $G$ be a multigraph whose $n$ vertices are the agents and whose $m$ edges form the item set $M$ (parallel edges allowed, no loops); $M_i$ is the set of edges incident with agent $i$. Every agent $i$ has a valuation $v_i$ on sets of items that is normalized ($v_i(\emptyset)=0$), monotone and subadditive ($v_i(S\cup T)\le v_i(S)+v_i(T)$), and depends only on the items incident with $i$: $v_i(T)=v_i(T\cap M_i)$ for every $T$. Let $\delta_i=\max_{e\in M} v_i(\{e\})$ be the largest value of a single item. $\mathrm{MMS}(M,v_i,k)$ is the maximum, over all ways of splitting $M$ into $k$ labelled, possibly empty bundles, of the smallest bundle value under $v_i$ (`LittleCharity.MMS.mms (v i) k univ`). An allocation is an orientation: each edge is given to one of its two endpoints. Then there is an orientation $o$ such that, for every agent $i$, the bundle $B_i=\{e : o(e)=i\}$ satisfies
--   $$v_i(B_i)\ \ge\ \frac{v_i(M)-\delta_i}{2},\qquad v_i(B_i)\ \ge\ \tfrac12\,\mathrm{MMS}(M,v_i,2)\ \ge\ \tfrac12\,\mathrm{MMS}(M,v_i,n).$$
--
--   Differences from the source:
--   - encoding: a multigraph G on the agents (parallel edges allowed) whose edges are the items; each agent has a valuation over M_i and 0 marginal value for every other item; allocations are orientations → Multigraph n m (edges Fin m with two distinct endpoints in Fin n), v : Fin n → Finset (Fin m) → ℝ with v i T = v i (T ∩ M_i) for all T (IsMultigraphInstance), and an orientation o : Fin m → Fin n with o e an endpoint of e, agent i receiving bundleOf o i = {e | o e = i}; reason: a direct transcription of §2.2; an edge joins two agents, so loops are not part of the model, and 0 marginal value outside M_i is exactly v_i(T) = v_i(T ∩ M_i)
--   - encoding: δ_i, the maximum value under v_i of any single item → maxItemValue (v i) Finset.univ: the maximum of v_i({e}) over all items e : Fin m, and 0 when there are no items; reason: M is the set of all items; with no items the maximum is undefined and both sides of the bound are 0 under the convention δ_i = 0
-- source:
--   Feige, arXiv:2506.21493v1, Corollary 14, p. 10

import Mathlib
import Definitions.Def_SubmodOrder_Subadditive
import Definitions.Def_LittleCharity_MMS_Setting
import Definitions.Def_MultiAllocToAlloc_Subadditive_Valuation
import Definitions.Def_MultiAllocToAlloc_Subadditive_Multigraph

namespace MultiAllocToAlloc.Subadditive

/-- Feige, arXiv:2506.21493v1, Corollary 14, p. 10: in a multigraph allocation instance with
normalized monotone subadditive valuations, where `δ_i` is the largest value of a single item
under `v_i`, there is an orientation in which every agent `i` receives a bundle of value at least
`(v_i(M) − δ_i)/2` and at least `½·MMS(M, v_i, 2)`, and `½·MMS(M, v_i, 2) ≥ ½·MMS(M, v_i, n)`. -/
theorem corollary_14 {n m : ℕ} (G : Multigraph n m) (v : Fin n → Finset (Fin m) → ℝ)
    (hnorm : ∀ i, IsNormalized (v i)) (hmono : ∀ i, IsMonotone (v i))
    (hsub : ∀ i, SubmodOrder.Subadditive (v i)) (hG : IsMultigraphInstance G v) :
    ∃ o : Fin m → Fin n, G.IsOrientation o ∧
      ∀ i : Fin n,
        (v i Finset.univ - maxItemValue (v i) Finset.univ) / 2 ≤ v i (bundleOf o i) ∧
        LittleCharity.MMS.mms (v i) 2 Finset.univ / 2 ≤ v i (bundleOf o i) ∧
        LittleCharity.MMS.mms (v i) n Finset.univ / 2 ≤
          LittleCharity.MMS.mms (v i) 2 Finset.univ / 2 := by sorry

end MultiAllocToAlloc.Subadditive

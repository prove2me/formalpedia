-- Prove2me | Theorems.Thm_LNTopology_Hermetic_lemma_B_1
-- name    : LNTopology.Hermetic.lemma_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:33:29.842873+00:00
-- url     : https://prove2.me/theorems/847fc776-ac41-4932-b3e2-27c4b57f1408
-- title:
--   Lemma B.1 — $U$ is hermetizable if $d(i)>g_+^{-1}(2c(S(i))/c(s(i)))$ for all $i\in U$
-- statement:
--   Let $c$ be a channel cost satisfying (MO), (SY), (CI), (SA) and (SA+) with the function $g_+$, let $\Lambda=(\lambda_{i,j})$ be a Lightning Network on the finite node set $V$, and let $U\subseteq V$ be a nonempty set of nodes each of which has at least one channel to another node of $U$. Write $d(i)$, $s(i)$, $S(i)$ for the degree, smallest and largest channel flow of $i$ in the subnetwork induced on $U$. If
--
--   $$d(i)>g_+^{-1}\!\left(2\,\frac{c(S(i))}{c(s(i))}\right)\qquad\text{for all }i\in U,$$
--
--   then $U$ is hermetizable: replacing the channels among the nodes of $U$ by channels to a new hub $v_0$ strictly reduces the cost of the network.
--
--   This is the basic sufficient condition for hermetization; Lemma B.2 and Theorem 3.8 reduce to it.
--
--   **Formalization Note** The condition is stated as $g_+(d(i))>2\,c(S(i))/c(s(i))$, which is equivalent to the paper's wherever $g_+^{-1}$ is defined ($g_+$ is strictly increasing but not assumed onto, so $g_+^{-1}$ need not be defined; the paper uses the same equivalence in its proof). Degrees, $s$ and $S$ are those of the subnetwork induced on $U$, as in the paper's proof, which sums over $U$ only. That $U$ is nonempty and that each $i\in U$ has a channel in $U$ are presupposed by the paper ($s(i)$ is otherwise undefined) and are stated explicitly. (SA) and (SA+) are in the corrected forms of the definition file.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Topology, SSRN 4439190 (version of Feb. 3, 2023), p. 11 (PDF p. 12), Lemma B.1

import Mathlib
import Definitions.Def_LNTopology_Hermetic_Model
import Definitions.Def_LNTopology_Hermetic_Degree
import Definitions.Def_LNTopology_Hermetic_Hermetization

namespace LNTopology.Hermetic

/-- Lemma B.1: a nonempty set `U` is hermetizable if every `i ∈ U` has a channel inside `U` and
`g₊(d_U(i)) > 2 c(S_U(i)) / c(s_U(i))` (the paper's `d(i) > g₊⁻¹(2 c(S(i))/c(s(i)))`), the degree
data being those of the subnetwork induced on `U`. -/
theorem lemma_B_1 {V : Type*} [Fintype V] [DecidableEq V] (c g : ℝ → ℝ)
    (hc : LNTopology.Local.IsChannelCost c) (hg : SAPlus c g) (Λ : V → V → ℝ) (hΛ : LNTopology.Local.IsLN Λ)
    (U : Finset V) (hU : U.Nonempty) (hch : ∀ i ∈ U, 1 ≤ degIn Λ U i)
    (hdeg : ∀ i ∈ U,
      2 * (c (maxFlowIn Λ U i) / c (minFlowIn Λ U i)) < g (degIn Λ U i : ℝ)) :
    IsHermetizable c Λ U := by sorry

end LNTopology.Hermetic

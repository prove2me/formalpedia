-- Prove2me | Theorems.Thm_LNTopology_RandomHerm_lemma_B_1
-- name    : LNTopology.RandomHerm.lemma_B_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T10:15:16.431972+00:00
-- url     : https://prove2.me/theorems/b37c787f-b5f1-4538-be0f-405d15288a6e
-- title:
--   Lemma B.1 — U is hermetizable if d(i) > g₊⁻¹(2c(S(i))/c(s(i))) for all i ∈ U
-- statement:
--   Let $c$ be a channel cost with (MO), (SY), (CI), (SA), and let $g_+$ satisfy (SA+) for $c$. Let $\Lambda$ be a Lightning Network on the finite node set $V$, and let $U\subseteq V$ be a nonempty set of nodes such that every $i\in U$ has at least one channel to another node of $U$. Write $d_U(i)$, $s_U(i)$, $S_U(i)$ for the degree and the smallest and largest channel sizes of $i$ in the subnetwork induced on $U$. If
--   $$g_+\big(d_U(i)\big)>2\,\frac{c(S_U(i))}{c(s_U(i))}\qquad\text{for all } i\in U,$$
--   then $U$ is hermetizable: hermetizing $U$ strictly reduces the cost of the network.
--
--   In the paper's notation the condition reads $d(i)>g_+^{-1}\big(2c(S(i))/c(s(i))\big)$. The lemma converts a local, node-by-node comparison of channel sizes into a global cost reduction, and it is the deterministic step behind both Theorem 3.8 and Theorem 3.9.
--
--   **Formalization Note** Degrees and channel sizes are those of the subnetwork induced on $U$, which is what the paper's proof uses (it sums over $U$ only). The condition $d(i)>g_+^{-1}(y)$ is stated as $g_+(d(i))>y$, because $g_+$ is strictly increasing but not assumed onto, so $g_+^{-1}$ need not be defined; the paper uses this equivalence in its proof. Nonemptiness of $U$ and the existence of a channel inside $U$ at each $i\in U$ are presupposed by the paper's condition (it mentions $s(i)$); they are explicit hypotheses here. (SA) and (SA+) are in their corrected forms (see the file `ChannelCost`).
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Topology, SSRN 4439190 (version of Feb. 3, 2023), p. 11 (PDF 12), Lemma B.1

import Mathlib
import Definitions.Def_LNTopology_Local_Model
import Definitions.Def_LNTopology_Hermetic_Model
import Definitions.Def_LNTopology_RandomHerm_ChannelCost
import Definitions.Def_LNTopology_RandomHerm_Hermetization

open MeasureTheory

namespace LNTopology.RandomHerm

/-- Lemma B.1 (p. 11): if every node `i` of a nonempty set `U` has a channel inside `U` and
`g₊(d_U(i)) > 2 c(S_U(i)) / c(s_U(i))` (the paper's `d(i) > g₊⁻¹(2c(S(i))/c(s(i)))`), with
degrees and channel sizes taken in the subnetwork induced on `U`, then `U` is hermetizable. -/
theorem lemma_B_1 {V : Type*} [Fintype V] [DecidableEq V] (c g : ℝ → ℝ) (Λ : V → V → ℝ)
    (U : Finset V) (hc : LNTopology.Local.IsChannelCost c) (hg : LNTopology.Hermetic.SAPlus c g) (hΛ : LNTopology.Local.IsLN Λ) (hU : U.Nonempty)
    (hdeg : ∀ i ∈ U, 1 ≤ degOn Λ U i)
    (hcond : ∀ i ∈ U, 2 * c (maxChanOn Λ U i) / c (minChanOn Λ U i) < g (degOn Λ U i)) :
    IsHermetizable c Λ U := by sorry

end LNTopology.RandomHerm

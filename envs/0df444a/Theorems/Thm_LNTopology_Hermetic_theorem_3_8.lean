-- Prove2me | Theorems.Thm_LNTopology_Hermetic_theorem_3_8
-- name    : LNTopology.Hermetic.theorem_3_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:33:51.450136+00:00
-- url     : https://prove2.me/theorems/d4ccc472-dbf2-4d23-9a36-eb82f5fee21c
-- title:
--   Theorem 3.8 — a Lightning Network with $\bar d(G)>2g_+^{-1}(2\,\mathrm{disc}(G))$ is hermetizable
-- statement:
--   Let $c$ be a channel cost satisfying (MO), (SY), (CI), (SA) and (SA+) with the function $g_+$, and let $G$ be a Lightning Network with flows $\Lambda=(\lambda_{i,j})$ on a nonempty finite node set $V$, having at least one channel. Let $\bar d(G)$ be its average degree and $\mathrm{disc}(G)$ its discrepancy. If
--
--   $$\bar d(G)\ >\ 2\,g_+^{-1}\big(2\,\mathrm{disc}(G)\big),$$
--
--   then $G$ is hermetizable: there is a set of nodes $U$ such that replacing the channels among the nodes of $U$ by channels to a new hub strictly reduces the cost of the network.
--
--   This is the paper's sufficient condition for a cost-reducing hub: a network that is dense relative to the spread of its channel flows always admits one.
--
--   **Formalization Note** The condition is stated as $g_+(\bar d(G)/2)>2\,\mathrm{disc}(G)$, equivalent to the paper's wherever $g_+^{-1}$ is defined. "At least one channel" is implied by the paper's hypothesis ($\bar d(G)>2g_+^{-1}(\cdot)\ge0$) but must be explicit in the $g_+$-form, where a network without channels would otherwise satisfy it with the junk value $\mathrm{disc}=0$. The discrepancy is the maximum over nodes having a channel. The theorem's second clause, the existence of a polynomial-time algorithm, is a complexity claim and is not formalized; the procedure itself is Lemma B.3. (SA) and (SA+) are in the corrected forms of the definition file.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Topology, SSRN 4439190 (version of Feb. 3, 2023), p. 8 (PDF p. 9), Theorem 3.8

import Mathlib
import Definitions.Def_LNTopology_Hermetic_Model
import Definitions.Def_LNTopology_Hermetic_Degree
import Definitions.Def_LNTopology_Hermetic_Hermetization

namespace LNTopology.Hermetic

/-- Theorem 3.8 (existence part): under (MO)–(SA+), a Lightning Network with at least one channel
and `g₊(d̄(G)/2) > 2 disc(G)` (the paper's `d̄(G) > 2 g₊⁻¹(2 disc(G))`) is hermetizable. -/
theorem theorem_3_8 {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (c g : ℝ → ℝ)
    (hc : LNTopology.Local.IsChannelCost c) (hg : SAPlus c g) (Λ : V → V → ℝ) (hΛ : LNTopology.Local.IsLN Λ)
    (hchan : ∃ u v, Λ u v ≠ 0)
    (hdisc : 2 * disc c Λ < g (avgDeg Λ / 2)) :
    IsHermetizableLN c Λ := by sorry

end LNTopology.Hermetic

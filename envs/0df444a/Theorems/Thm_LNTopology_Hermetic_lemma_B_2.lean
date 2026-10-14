-- Prove2me | Theorems.Thm_LNTopology_Hermetic_lemma_B_2
-- name    : LNTopology.Hermetic.lemma_B_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:33:43.909967+00:00
-- url     : https://prove2.me/theorems/34dcabb6-6ac8-4f8c-bbda-1ef3c53a3383
-- title:
--   Lemma B.2 — $U$ is hermetizable if $\delta(U)\ge g_+^{-1}(2\,\mathrm{disc}(U))$
-- statement:
--   Let $c$ be a channel cost satisfying (MO), (SY), (CI), (SA) and (SA+) with the function $g_+$, let $\Lambda$ be a Lightning Network on the finite node set $V$, and let $U\subseteq V$ be a nonempty set of nodes each of which has at least one channel to another node of $U$. Let $\delta(U)$ be the minimum degree and $\mathrm{disc}(U)$ the discrepancy of the subnetwork induced on $U$. If
--
--   $$\delta(U)\ \ge\ g_+^{-1}\big(2\,\mathrm{disc}(U)\big),$$
--
--   then $U$ is hermetizable.
--
--   The lemma replaces the node-by-node condition of Lemma B.1 by a single condition on the minimum degree and the discrepancy; Theorem 3.8 applies it to a dense subnetwork.
--
--   **Formalization Note** The condition is stated as $g_+(\delta(U))\ge 2\,\mathrm{disc}(U)$, equivalent to the paper's wherever $g_+^{-1}$ is defined. The inequality is weak, as printed. Nonemptiness of $U$ and the existence of a channel in $U$ at every node of $U$ are presupposed by the paper ($s$ and the discrepancy are otherwise undefined) and are stated explicitly. (SA) and (SA+) are in the corrected forms of the definition file.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Topology, SSRN 4439190 (version of Feb. 3, 2023), p. 12 (PDF p. 13), Lemma B.2

import Mathlib
import Definitions.Def_LNTopology_Hermetic_Model
import Definitions.Def_LNTopology_Hermetic_Degree
import Definitions.Def_LNTopology_Hermetic_Hermetization

namespace LNTopology.Hermetic

/-- Lemma B.2: a nonempty set `U` in which every node has a channel inside `U` is hermetizable if
`g₊(δ(U)) ≥ 2 disc(U)` (the paper's `δ(U) ≥ g₊⁻¹(2 disc(U))`), with `δ(U)` and `disc(U)` computed
in the subnetwork induced on `U`. -/
theorem lemma_B_2 {V : Type*} [Fintype V] [DecidableEq V] (c g : ℝ → ℝ)
    (hc : LNTopology.Local.IsChannelCost c) (hg : SAPlus c g) (Λ : V → V → ℝ) (hΛ : LNTopology.Local.IsLN Λ)
    (U : Finset V) (hU : U.Nonempty) (hch : ∀ i ∈ U, 1 ≤ degIn Λ U i)
    (hmin : 2 * discIn c Λ U ≤ g (minDegIn Λ U : ℝ)) :
    IsHermetizable c Λ U := by sorry

end LNTopology.Hermetic

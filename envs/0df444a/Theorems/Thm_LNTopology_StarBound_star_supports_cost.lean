-- Prove2me | Theorems.Thm_LNTopology_StarBound_star_supports_cost
-- name    : LNTopology.StarBound.star_supports_cost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:32:21.297464+00:00
-- url     : https://prove2.me/theorems/c857baa8-81ce-4dd9-91ee-cc0eb7fe7d2b
-- title:
--   Proof of Theorem 3.10, pp. 13–14 — the star supports $\mathcal F$ and costs $\sum_i c(f_i)-c(f_h)$
-- statement:
--   Let $V$ be a finite set of nodes, $c$ a channel cost function satisfying (MO), (SY), (CI) and (SA), and $\mathcal F=(f_i)_{i\in V}$ a payment flow with
--   $$\sum_{i\in V}f_i=0 .$$
--   Then for every hub $h\in V$, the star $\Lambda^{h}$ centered at $h$
--   1. is a Lightning Network (anti-symmetric),
--   2. supports $\mathcal F$, and
--   3. has cost
--   $$c(\Lambda^{h})=\sum_{i\in V}c(f_i)-c(f_h).$$
--
--   This is the construction behind the upper bound of Theorem 3.10 and behind Corollary 3.12: choosing a hub with $c(f_h)=\max_i c(f_i)$ gives a supporting network of cost $\sum_i c(f_i)-\max_i c(f_i)$.
--
--   **Formalization Note.** The paper fixes the hub with $f_0=\max_i f_i$ and then writes $c(f_0)=\max_i c(f_i)$; this fails when the most negative flow has the larger magnitude. The statement here holds for every hub, which is what the paper's computation $\sum_{i=0}^n c(f_i)-c(f_0)$ shows; the hub maximizing $c(f_h)$ is chosen in Theorem 3.10. The star uses $\lambda_{i,h}=f_i$ (the paper writes $\lambda_{0,i}=f_i$, the opposite sign under the row-sum convention); the cost is the same by (SY). (SA) is in its corrected form, for all $x,y>0$.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Topology, SSRN 4439190 (version of Feb. 3, 2023), pp. 13–14 (PDF 14–15), App. C, proof of Theorem 3.10 (upper bound)

import Mathlib
import Definitions.Def_LNTopology_StarBound_Model
import Definitions.Def_LNTopology_Local_Star

namespace LNTopology.StarBound

/-- Proof of Theorem 3.10, pp. 13–14: when `∑ i, f i = 0`, the LNTopology.Local.star centered at any hub `h`
is a Lightning Network that supports `f`, and its cost is `∑_i c (f i) - c (f h)`. -/
theorem star_supports_cost {V : Type*} [Fintype V] [DecidableEq V] (c : ℝ → ℝ)
    (hc : IsChannelCost c) (f : V → ℝ) (hf : ∑ i, f i = 0) (h : V) :
    IsLN (LNTopology.Local.star f h) ∧ Supports (LNTopology.Local.star f h) f ∧
      cost c (LNTopology.Local.star f h) = ∑ i, c (f i) - c (f h) := by sorry

end LNTopology.StarBound

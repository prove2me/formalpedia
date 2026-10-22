-- Prove2me | Theorems.Thm_LNTopology_StarBound_corollary_3_12
-- name    : LNTopology.StarBound.corollary_3_12
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:33:11.25971+00:00
-- url     : https://prove2.me/theorems/c890b949-c644-4fc5-b425-2e4c1d567ba8
-- title:
--   Corollary 3.12 — a star topology costs at most $2\cdot c_{\min}(\mathcal F)$
-- statement:
--   Let $V$ be a finite set of nodes, $c$ a channel cost function satisfying (MO), (SY), (CI) and (SA), and $\mathcal F=(f_i)_{i\in V}$ a payment flow with $\sum_{i\in V}f_i=0$. For every hub $h\in V$, the star $\Lambda^{h}$ centered at $h$ (each node $i\neq h$ has a single channel, to $h$, carrying its flow $f_i$) satisfies
--   $$c(\Lambda^{h})\;\le\;2\,c_{\min}(\mathcal F),$$
--   where $c_{\min}(\mathcal F)$ is the minimal cost of a Lightning Network on $V$ that supports $\mathcal F$.
--
--   The star is the natural candidate for a cost-minimal topology; Corollary 3.11 shows it is generally not optimal, and this corollary shows that it is never worse than optimal by more than a factor of two, for every cost function satisfying the axioms.
--
--   **Formalization Note.** The bound is stated for every hub, matching the paper's sentence "the star topology is at most twice as costly as the minimum"; the paper's proof uses one particular hub. $c_{\min}$ is an infimum over Lightning Networks on the same node set (the paper's "min" need not be attained when $c$ is discontinuous). The hypothesis $\sum_i f_i=0$ is the model's standing identity (§2, p. 4) and is required: without it $c_{\min}$ is a junk value. (SA) is in its corrected form, for all $x,y>0$ (the printed range $x>y\ge0$ is unsatisfiable, which would make the statement vacuous).
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Topology, SSRN 4439190 (version of Feb. 3, 2023), p. 9 (PDF 10), Corollary 3.12; proof p. 14 (PDF 15), App. C

import Mathlib
import Definitions.Def_LNTopology_StarBound_Model
import Definitions.Def_LNTopology_StarBound_MinCost
import Definitions.Def_LNTopology_Local_Star

namespace LNTopology.StarBound

/-- Corollary 3.12, p. 9: for any flow `f` (with `∑ i, f i = 0`), the LNTopology.Local.star centered at any hub
costs at most twice the minimal cost of a Lightning Network supporting `f`. -/
theorem corollary_3_12 {V : Type*} [Fintype V] [DecidableEq V] (c : ℝ → ℝ)
    (hc : IsChannelCost c) (f : V → ℝ) (hf : ∑ i, f i = 0) (h : V) :
    cost c (LNTopology.Local.star f h) ≤ 2 * cmin c f := by sorry

end LNTopology.StarBound

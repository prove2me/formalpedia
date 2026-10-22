-- Prove2me | Theorems.Thm_LNTopology_StarBound_theorem_3_10
-- name    : LNTopology.StarBound.theorem_3_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:33:13.155554+00:00
-- url     : https://prove2.me/theorems/9af182c2-45d4-4bfd-855b-c5aedcfadae8
-- title:
--   Theorem 3.10 — $\sum_i c(f_i)-\max_i c(f_i)\ge c_{\min}(\mathcal F)\ge\max\big(\sum_{f_i>0}c(f_i),\sum_{f_i<0}c(f_i)\big)$
-- statement:
--   Let $V$ be a nonempty finite set of nodes, $c$ a channel cost function satisfying (MO), (SY), (CI) and (SA), and $\mathcal F=(f_i)_{i\in V}$ a payment flow with $\sum_{i\in V}f_i=0$. Then the minimal cost $c_{\min}(\mathcal F)$ of a Lightning Network on $V$ supporting $\mathcal F$ satisfies
--   $$\sum_{i\in V}c(f_i)-\max_{i\in V}c(f_i)\;\ge\;c_{\min}(\mathcal F)\;\ge\;\max\Big(\sum_{f_i>0}c(f_i),\ \sum_{f_i<0}c(f_i)\Big).$$
--
--   The two bounds locate the globally minimal cost without computing it: the upper bound is achieved by a star topology, and the lower bound comes from the fact that each payer's (or each payee's) flow must be carried by its own channels.
--
--   **Formalization Note.** $c_{\min}$ is an infimum, since the paper's "min" need not be attained for a discontinuous $c$. The hypothesis $\sum_i f_i=0$ is the model's standing identity (§2, p. 4); without it no network supports $\mathcal F$ and $c_{\min}$ would be a junk value. Nonemptiness of $V$ is needed for $\max_{i\in V}$. (SA) is in its corrected form, for all $x,y>0$. The statement is symmetric under $\mathcal F\mapsto-\mathcal F$, so the row-sum sign convention is immaterial.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Topology, SSRN 4439190 (version of Feb. 3, 2023), p. 8 (PDF 9), Theorem 3.10

import Mathlib
import Definitions.Def_LNTopology_StarBound_Model
import Definitions.Def_LNTopology_StarBound_MinCost

namespace LNTopology.StarBound

/-- Theorem 3.10, p. 8: for a flow `f` with `∑ i, f i = 0` on a nonempty finite node set,
`∑_i c(f_i) - max_i c(f_i) ≥ c_min(f) ≥ max(∑_{f_i>0} c(f_i), ∑_{f_i<0} c(f_i))`. -/
theorem theorem_3_10 {V : Type*} [Fintype V] [Nonempty V] (c : ℝ → ℝ) (hc : IsChannelCost c)
    (f : V → ℝ) (hf : ∑ i, f i = 0) :
    cmin c f ≤ ∑ i, c (f i) - Finset.univ.sup' Finset.univ_nonempty (fun i => c (f i)) ∧
      max (∑ i ∈ Finset.univ.filter (fun i => 0 < f i), c (f i))
          (∑ i ∈ Finset.univ.filter (fun i => f i < 0), c (f i)) ≤ cmin c f := by sorry

end LNTopology.StarBound

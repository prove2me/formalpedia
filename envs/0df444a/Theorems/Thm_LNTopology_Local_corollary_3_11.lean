-- Prove2me | Theorems.Thm_LNTopology_Local_corollary_3_11
-- name    : LNTopology.Local.corollary_3_11
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T06:27:40.969894+00:00
-- url     : https://prove2.me/theorems/49b5bae2-f691-409d-8f17-ad16b7029df3
-- title:
--   Corollary 3.11, p. 9 — with two net payers and two net payees, no star is cost-minimizing
-- statement:
--   Let $c$ be a channel cost function satisfying (MO), (SY), (CI) and (SA), and let $F=(f_i)_{i\in V}$ be a payment flow on a finite node set with $\sum_i f_i=0$. Suppose there are distinct nodes $i_1\neq i_2$ and distinct nodes $j_1\neq j_2$ with
--   $$
--   f_{i_1},\,f_{i_2}>0>f_{j_1},\,f_{j_2}.
--   $$
--   Then for every hub $h\in V$, the star with hub $h$ (each node $i\ne h$ joined only to $h$, by a channel carrying its own net flow) is not cost-minimizing for $F$.
--
--   The star topology is the natural guess for a globally cheapest network; this corollary of Theorem 3.1 shows it is cost-minimizing only when there is a single net payer or a single net payee.
--
--   **Formalization Note** The hypothesis $\sum_i f_i=0$ (p. 4: "the sum of all the flows is 0") is stated because no network is given: it is what makes the star support $F$. Under the row-sum convention a node with $f_i>0$ is a net payer; the statement is symmetric under $F\mapsto-F$, so the paper's opposite sign convention gives the same theorem. (SA) is used in the corrected form for all $x,y>0$ (the printed range is unsatisfiable). Cost-minimizing compares with networks on the same node set.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Topology, SSRN 4439190 (version of Feb. 3, 2023), p. 9 (PDF 10), Corollary 3.11; proof p. 13 (PDF 14), App. C

import Mathlib
import Definitions.Def_LNTopology_Local_Model
import Definitions.Def_LNTopology_Local_Star

namespace LNTopology.Local

/-- Corollary 3.11 (SSRN 4439190, p. 9; proof p. 13): if the flow `f` (summing to zero) has two
distinct nodes with positive flow and two distinct nodes with negative flow, then no star
network, whatever its hub, is cost-minimizing for `f`. -/
theorem corollary_3_11 {V : Type*} [Fintype V] [DecidableEq V] (c : ℝ → ℝ)
    (hc : IsChannelCost c) (f : V → ℝ) (hsum : ∑ i, f i = 0)
    (i₁ i₂ j₁ j₂ : V) (hi : i₁ ≠ i₂) (hj : j₁ ≠ j₂)
    (hi₁ : 0 < f i₁) (hi₂ : 0 < f i₂) (hj₁ : f j₁ < 0) (hj₂ : f j₂ < 0) :
    ∀ h : V, ¬ IsCostMinimizing c f (star f h) := by sorry

end LNTopology.Local

-- Prove2me | Theorems.Thm_LNTopology_Local_corollary_3_3
-- name    : LNTopology.Local.corollary_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:28:04.642155+00:00
-- url     : https://prove2.me/theorems/2f703131-0ce4-4959-ace9-da90d15b512b
-- title:
--   Corollary 3.3, p. 6 — a cost-minimizing Lightning Network is bipartite, with all net flows from A to B
-- statement:
--   Let $c$ be a channel cost function satisfying (MO), (SY), (CI) and (SA), and let $\Lambda=(\lambda_{i,j})$ be a Lightning Network on a finite node set $V$ that is cost-minimizing for a payment flow $F$. Then there is a set $A\subseteq V$, with complement $B=V\setminus A$, such that
--
--   1. the channel graph of $\Lambda$ — nodes $V$, an edge between $i$ and $j$ whenever $\lambda_{i,j}\neq0$ — is bipartite with parts $A$ and $B$; and
--   2. every net flow goes from $A$ to $B$:
--   $$
--   \lambda_{i,j}>0\ \Longrightarrow\ i\in A\ \text{and}\ j\in B .
--   $$
--
--   This is the structural conclusion of §3.1: in a cost-minimizing Lightning Network, the nodes split into pure senders and pure receivers, and every channel joins a sender to a receiver.
--
--   **Formalization Note** The bipartite clause uses Mathlib's `SimpleGraph.IsBipartiteWith A Aᶜ` on `SimpleGraph.fromRel (fun a b => Λ a b ≠ 0)`. The flow-direction clause is the stronger content and is stated separately. The statement is conditional: it does not claim that a cost-minimizing network exists. (SA) is used in the corrected form for all $x,y>0$ (the printed range is unsatisfiable). Cost-minimizing compares with networks on the same node set.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Topology, SSRN 4439190 (version of Feb. 3, 2023), p. 6 (PDF 7), Corollary 3.3; proof p. 10 (PDF 11), App. A

import Mathlib
import Definitions.Def_LNTopology_Local_Model

namespace LNTopology.Local

/-- Corollary 3.3 (SSRN 4439190, p. 6; proof p. 10): a cost-minimizing Lightning Network is a
bipartite graph with parts `A` and `B = Aᶜ` in which every net flow goes from `A` to `B`. -/
theorem corollary_3_3 {V : Type*} [Fintype V] (c : ℝ → ℝ) (hc : IsChannelCost c)
    (f : V → ℝ) (Λ : V → V → ℝ) (hmin : IsCostMinimizing c f Λ) :
    ∃ A : Set V, (SimpleGraph.fromRel (fun a b => Λ a b ≠ 0)).IsBipartiteWith A Aᶜ ∧
      ∀ i j, 0 < Λ i j → i ∈ A ∧ j ∉ A := by sorry

end LNTopology.Local

-- Prove2me | Theorems.Thm_LNTopology_Local_in_and_out
-- name    : LNTopology.Local.in_and_out
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:27:41.389218+00:00
-- url     : https://prove2.me/theorems/50c7cd21-f21c-4e17-bcb9-befe854e0993
-- title:
--   Proof of Corollary 3.2, p. 10 — a node with an incoming and an outgoing channel makes any network non-cost-minimizing
-- statement:
--   Let $c$ be a channel cost function satisfying (MO), (SY), (CI) and (SA), let $\Lambda=(\lambda_{i,j})$ be a Lightning Network on a finite node set $V$ supporting the flow $F$, and suppose some node $v$ has an incoming and an outgoing channel: there are nodes $u,w$ with
--   $$
--   \lambda_{u,v}>0\quad\text{and}\quad\lambda_{v,w}>0 .
--   $$
--   Then $\Lambda$ is not cost-minimizing for $F$: some Lightning Network on $V$ supporting $F$ has strictly smaller cost.
--
--   This is Theorem 3.1 as the paper uses it in the proofs of Corollaries 3.2 and 3.3 and in Appendix C: inside an arbitrary network, where $u$ and $w$ may already share a channel and other channels are present, a relaying node still makes the network non-optimal.
--
--   **Formalization Note** Nothing is assumed about the rest of $\Lambda$, in particular $\lambda_{u,w}$ may be nonzero. Node distinctness need not be assumed: $u\ne v\ne w$ and $u\ne w$ follow from anti-symmetry. (SA) is used in the corrected form for all $x,y>0$ (the printed range is unsatisfiable). Cost-minimizing compares with networks on the same node set.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Topology, SSRN 4439190 (version of Feb. 3, 2023), p. 10 (PDF 11), App. A, proof of Corollary 3.2 (application of Theorem 3.1)

import Mathlib
import Definitions.Def_LNTopology_Local_Model

namespace LNTopology.Local

/-- The in-and-out claim (proof of Corollary 3.2, SSRN 4439190, p. 10), i.e. Theorem 3.1 inside
an arbitrary network: if a node `v` of a Lightning Network `Λ` supporting `f` has an incoming
channel (`0 < Λ u v`) and an outgoing channel (`0 < Λ v w`), then `Λ` is not cost-minimizing
for `f`. -/
theorem in_and_out {V : Type*} [Fintype V] (c : ℝ → ℝ) (hc : IsChannelCost c)
    (f : V → ℝ) (Λ : V → V → ℝ) (hΛ : IsLN Λ) (hsupp : Supports Λ f) (u v w : V)
    (huv : 0 < Λ u v) (hvw : 0 < Λ v w) :
    ¬ IsCostMinimizing c f Λ := by sorry

end LNTopology.Local

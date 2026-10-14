-- Prove2me | Theorems.Thm_LNTopology_StarBound_node_subadditivity
-- name    : LNTopology.StarBound.node_subadditivity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:32:33.346166+00:00
-- url     : https://prove2.me/theorems/a57df920-9ca1-4e6b-9d1e-331fd8331273
-- title:
--   Proof of Theorem 3.10, p. 14 — a node's channels cost at least the cost of its net flow
-- statement:
--   Let $V$ be a finite set of nodes, $c$ a channel cost function satisfying (MO), (SY), (CI) and (SA), and $\mathcal F=(f_i)_{i\in V}$ a payment flow. Let $\Lambda=(\lambda_{i,j})$ be a matrix with $\sum_{j\in V}\lambda_{i,j}=f_i$ for every node $i$. Then for every node $i$,
--   $$\sum_{j\in V}c(\lambda_{i,j})\;\ge\;c\Big(\sum_{j\in V}\lambda_{i,j}\Big)=c(f_i).$$
--
--   This is the first step of the lower bound in Theorem 3.10: the channels of a single node cost at least as much as one channel carrying that node's net flow.
--
--   **Formalization Note.** The channel flows $\lambda_{i,j}$ have mixed signs, so the inequality is a many-term consequence of (MO), (SY), (CI) and (SA) together, not the two-term axiom (SA) itself. Anti-symmetry of $\Lambda$ is not needed and not assumed. (SA) is used in its corrected form, for all $x,y>0$ (the printed range $x>y\ge0$ is unsatisfiable).
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Topology, SSRN 4439190 (version of Feb. 3, 2023), p. 14 (PDF 15), App. C, proof of Theorem 3.10 (lower bound, first paragraph)

import Mathlib
import Definitions.Def_LNTopology_StarBound_Model

namespace LNTopology.StarBound

/-- Proof of Theorem 3.10, p. 14: for a network supporting `f`, the cost of node `i`'s
channels is at least the cost of its net flow, `c (f i) ≤ ∑_j c (Λ i j)`. -/
theorem node_subadditivity {V : Type*} [Fintype V] (c : ℝ → ℝ) (hc : IsChannelCost c)
    (f : V → ℝ) (Λ : V → V → ℝ) (hΛ : Supports Λ f) (i : V) :
    c (f i) ≤ ∑ j, c (Λ i j) := by sorry

end LNTopology.StarBound

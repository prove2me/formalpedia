-- Prove2me | Theorems.Thm_LNTopology_Local_corollary_3_2
-- name    : LNTopology.Local.corollary_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:27:53.597043+00:00
-- url     : https://prove2.me/theorems/0eeed2cb-5ad1-4176-bc51-91a4a450cfed
-- title:
--   Corollary 3.2, p. 6 — an odd cycle is not cost-minimizing
-- statement:
--   Let $c$ be a channel cost function satisfying (MO), (SY), (CI) and (SA), and let $\Lambda=(\lambda_{i,j})$ be a Lightning Network on a finite node set $V$ supporting the flow $F$. Suppose $\Lambda$ contains a cycle of odd length $k\ge3$: distinct nodes $u_1,\dots,u_k$ with a channel between $u_j$ and $u_{j+1}$ for $1\le j<k$ and between $u_k$ and $u_1$, the flow in each channel going in either direction,
--   $$
--   \lambda_{u_j,u_{j+1}}\neq 0\ (1\le j<k),\qquad \lambda_{u_k,u_1}\neq0 .
--   $$
--   Then $\Lambda$ is not cost-minimizing for $F$.
--
--   Together with König's characterization of bipartite graphs, this gives Corollary 3.3: the channel graph of a cost-minimizing network has no odd cycle.
--
--   **Formalization Note** The cycle is a map $u:\{0,\dots,k-1\}\to V$ (`Fin k`), injective, with successor given by `finRotate k` ($j\mapsto j+1$, and $k-1\mapsto 0$). "A channel connects" is read as a nonzero net flow, in either direction. (SA) is used in the corrected form for all $x,y>0$ (the printed range is unsatisfiable). Cost-minimizing compares with networks on the same node set.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Topology, SSRN 4439190 (version of Feb. 3, 2023), p. 6 (PDF 7), Corollary 3.2; proof p. 10 (PDF 11), App. A

import Mathlib
import Definitions.Def_LNTopology_Local_Model

namespace LNTopology.Local

/-- Corollary 3.2 (SSRN 4439190, p. 6; proof p. 10): a Lightning Network containing a cycle of
odd length `k` — distinct nodes `u 0, …, u (k-1)` with a channel (nonzero net flow, in either
direction) between `u j` and its cyclic successor `u (finRotate k j)` — is not cost-minimizing. -/
theorem corollary_3_2 {V : Type*} [Fintype V] (c : ℝ → ℝ) (hc : IsChannelCost c)
    (f : V → ℝ) (Λ : V → V → ℝ) (hΛ : IsLN Λ) (hsupp : Supports Λ f)
    (k : ℕ) (hk : 3 ≤ k) (hodd : Odd k) (u : Fin k → V) (hu : Function.Injective u)
    (hcyc : ∀ j : Fin k, Λ (u j) (u (finRotate k j)) ≠ 0) :
    ¬ IsCostMinimizing c f Λ := by sorry

end LNTopology.Local

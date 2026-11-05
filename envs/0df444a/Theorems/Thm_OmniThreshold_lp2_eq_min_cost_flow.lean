-- Prove2me | Theorems.Thm_OmniThreshold_lp2_eq_min_cost_flow
-- name    : OmniThreshold.lp2_eq_min_cost_flow
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:36:07.174196+00:00
-- url     : https://prove2.me/theorems/db2ab757-9745-4570-a228-586ab7c72dab
-- title:
--   Proof of Theorem 2, p.10 — LP (2) is a min-cost flow problem on the bipartite fulfillment network
-- statement:
--   Let $s_{ji}\ge0$ and $s_{ji}<c_i$. Let $A^O\in\mathbb N^n$ be the accepted orders, and let $K\in\mathbb N$ satisfy $K\ge\sum_iA_i^O$. The optimal value of LP (2) equals the min-cost flow value of the bipartite fulfillment network. In that network:
--
--   1. the order node of location $i$ has supply $A_i^O$;
--   2. the arc from the store node $j$ to the sink has capacity $u_j=\mathcal I_j-\min(\mathcal I_j,\mathcal D_j^P)$, the unsold inventory at $j$;
--   3. every other arc has capacity $K$;
--   4. the sink has demand $\sum_iA_i^O$.
--
--   In particular, this flow value is finite.
--
--   This reformulation is what lets the proof of Theorem 2 apply Lemma 1 to the fulfillment cost.
--
--   Differences from the source:
--   - encoding: "an unlimited capacity on the arc between the cancellation node and the sink", and no stated capacity on the arcs out of the order nodes → capacity $K$ on these arcs, for every integer $K\ge\sum_iA_i^O$; reason: Lemma 1's capacities are integers, and no feasible flow carries more than $\sum_iA_i^O$ on any arc, so every such $K$ gives the uncapacitated value
--   - generalization: a single cancellation cost $c>\max\{s_{ji}\}$ → per-location costs with $s_{ji}<c_i$; reason: LP (2) has per-location $c_i$; the paper's assumption is the case $c_i=c$
--   - reading: shipping costs (no sign stated) → $s_{ji}\ge0$; reason: they are costs in the model of §1.1
--   - reading: the page does not list the arcs out of the location nodes on the first side, nor any arc cost → an arc from every order node $i$ to every store node $j$ with cost $s_{ji}$, an arc from every order node $i$ to the cancellation node with cost $c_i$, and cost $0$ on the arcs into the sink; reason: these are the arcs and costs that make the network express LP (2), whose variables are $F_{ji}$ and $C_i$
-- source:
--   Jia, Karp, Ravi & Tayur, Effective Online Order Acceptance Policies for Omni-Channel Fulfillment, SSRN 3932692, proof of Theorem 2, p.10, "LP (2) may be viewed as a minimum cost, single-commodity flow problem in a bipartite network …"

import Mathlib
import Definitions.Def_OmniThreshold_lp2Value
import Definitions.Def_OmniThreshold_minCostFlowValue
import Definitions.Def_OmniThreshold_fulfillmentNetwork

namespace OmniThreshold

/-- **Proof of Theorem 2, p.10: LP (2) is a minimum-cost flow problem** (Jia, Karp, Ravi & Tayur,
*Effective Online Order Acceptance Policies for Omni-Channel Fulfillment*, SSRN 3932692, proof of
Theorem 2, p.10: "LP (2) may be viewed as a minimum cost, single-commodity flow problem in a
bipartite network where nodes corresponding to each location are on one side of the bipartition and
have supplies equal to the number of accepted orders at that location. … The sink node has demand
equal to the sum of the supplies on the nodes representing accepted orders.").

For accepted orders `A`, the optimal value of LP (2) equals the min-cost flow value of the network
`fulfillmentNetwork` with supplies `A_i` at the order nodes, sink demand `∑_i A_i`, capacities
`u_j = I_j − min(I_j, D_j^P)` (the unsold inventory) on the store-to-sink arcs, and any capacity
`K ≥ ∑_i A_i` on the remaining arcs. In particular that flow value is finite.

**Formalization Note** The paper's "unlimited" capacity is encoded by every natural capacity
`K ≥ ∑_i A_i`, which no feasible flow can exceed. The cost assumptions `s_ji ≥ 0`, `s_ji < c_i` are
the model's (p.4). -/
theorem lp2_eq_min_cost_flow {n : ℕ} (I : Fin n → ℕ) (c : Fin n → ℝ) (s : Fin n → Fin n → ℝ)
    (hs : ∀ i j, 0 ≤ s j i) (hsc : ∀ i j, s j i < c i) (DP A : Fin n → ℕ) (K : ℕ)
    (hK : ∑ i, A i ≤ K) :
    ((lp2Value c s I DP A : ℝ) : WithTop ℝ) =
      minCostFlowValue (fulfillmentNetwork c s (fun j => I j - min (I j) (DP j)) K)
        Sum.inl (Sum.inr (Sum.inr true)) A := by sorry

end OmniThreshold

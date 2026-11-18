-- Prove2me | Theorems.Thm_OWMR_fifo_physical_upper_bound
-- name    : OWMR.fifo_physical_upper_bound
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-16T01:17:29.808203+00:00
-- url     : https://prove2.me/theorems/2774d997-9833-48e5-86fa-bbfb330cf965
-- title:
--   Physical upper bound for $\pi_{\rm FIFO}$ (Proposition 2)
-- statement:
--   This is the physical upper bound for the deterministic FIFO policy (Proposition 2 of the source).
--
--   Consider an OWMR network with $n\ge1$ retailers that satisfies the standing assumptions, a valid initial state $x$, and admissible choices for the FIFO policy $\pi_{\rm FIFO}$ of Definition 1 (canonical optima, best half windows, mirror centers $a_i$, and the supplier pair $(s_0,S_0)$). Let $(s_i,S_i)$ be the $(s,S)$ pair that retailer $i$ operates, and let
--
--   $$\mathcal L_i=\mathcal C_i(s_i,S_i)+\mathcal M_i(s_i,S_i)$$
--
--   be its augmented cost: the long-run average cost $\mathcal C_i$ of the $(s_i,S_i)$ policy in retailer $i$'s single-location problem with actual setup cost $K_i$ and holding and backlog cost $F_i$, plus its mirror cost $\mathcal M_i$, the minimum over centers $a$ of the long-run average of $\phi(a-\widehat P_{i,t})$, where $\phi(y)=hy^++py^-$ and $\widehat P_{i,t}$ is the retailer's position including outstanding requests. Then
--
--   $$C(\pi_{\rm FIFO})\le J_0(K_0+K_{\max})+\sum_{i=1}^n\mathcal L_i,$$
--
--   where $C(\pi_{\rm FIFO})$ is the long-run average expected cost from $x$, $K_{\max}=\max_iK_i$, and $J_0(k)$ is the optimal average cost of the supplier's single-location problem with aggregate demand, cost $f_{L_0}$, and setup cost $k$.
--
--   The supplier is charged one single-location problem at the inflated setup cost $K_0+K_{\max}$, which pays for continuation shipments, and each retailer is charged its own augmented cost. With the retailer comparison and the shared-cost lower bound (Proposition 3), this bound yields Theorem 1.
--
--   **Formalization Note** Costs are extended nonnegative reals. The augmented cost is `N.augCost i (c.s i) (c.S i)`, the sum of `ssAvgCost` at setup cost $K_i$ and `mirrorCost`; a retailer with $K_i=0$ uses base stock ($s_i=S_i$).
-- source:
--   M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse Multi-Retailer Systems", working paper (manuscript of November 2026), Section 5.2, Proposition 2 (Physical Upper Bound), eq. (27), p. 23; proved in Appendix B (p. E.4).

import Definitions.Def_owmr_fifo_policy

open scoped ENNReal

namespace OWMR
theorem fifo_physical_upper_bound {n : ℕ} (hn : 0 < n) (N : Network n) (hN : N.Standing)
    (x : InitState n) (hx : x.Valid) (c : FIFOChoice n) (hc : IsFIFOChoice N c) :
    (fifoPolicy N x c).avgCost N x ≤ N.J0 (N.K0 + N.Kmax) + ∑ i, N.augCost i (c.s i) (c.S i) := by sorry
end OWMR

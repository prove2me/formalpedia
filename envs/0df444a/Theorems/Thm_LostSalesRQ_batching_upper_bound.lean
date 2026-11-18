-- Prove2me | Theorems.Thm_LostSalesRQ_batching_upper_bound
-- name    : LostSalesRQ.batching_upper_bound
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-17T18:32:50.647381+00:00
-- url     : https://prove2.me/theorems/b58280ce-3869-4974-9aff-e9d7029e6d42
-- title:
--   Eq. (23): cost of batching the selected base-stock policy
-- statement:
--   Fix $\mu\ge0$, $a\ge0$, $k\ge0$, an integer base-stock level $j\ge1$ and a demand environment of rate one, and let $Q_k=\max\{1,\lfloor\sqrt{2k}\rfloor\}$, $b_k=(Q_k-1)/2+k/Q_k$. Every policy following the $(j-1,Q_k)$ rule satisfies
--   $$C_{\mu,a,k}(\pi_{\rm rQ}(j-1,Q_k))\le L_j(a)+b_k,\qquad\text{and}\qquad b_k\le\sqrt{2k}.$$
--
--   The surcharge $(Q_k-1)/2$ is the extra inventory from traversing $Q_k$ inventory positions and $k/Q_k$ spreads the setup charge over a lot, the same tradeoff as in the EOQ formula.
-- source:
--   M. Hu, "A 1.932 Guarantee for (r,Q) Policies in Continuous-Review Lost-Sales Inventory Systems", arXiv:2610.34576, 2026; Section 4.6.1, eq. (23) (p. 21); Appendix J.2 (pp. A22-A24).

import Definitions.Def_LostSalesRQ_model

namespace LostSalesRQ

theorem batching_upper_bound (μ a k : ℝ) (hμ : 0 ≤ μ) (ha : 0 ≤ a) (hk : 0 ≤ k)
    (S : DemandSpace 1) (j : ℕ) (hj : 1 ≤ j) (π : Policy S)
    (hπ : IsRQPolicy μ (j - 1) (lotSize k) π) :
    π.avgCost μ 1 a k ≤ ENNReal.ofReal (baseStockCost μ a j + batchSurcharge k) ∧
    batchSurcharge k ≤ Real.sqrt (2 * k) := by sorry

end LostSalesRQ

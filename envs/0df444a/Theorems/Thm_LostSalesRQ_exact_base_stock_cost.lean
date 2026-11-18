-- Prove2me | Theorems.Thm_LostSalesRQ_exact_base_stock_cost
-- name    : LostSalesRQ.exact_base_stock_cost
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-17T18:23:54.152199+00:00
-- url     : https://prove2.me/theorems/206c9090-703e-48ed-9b60-a54ac0ca3d57
-- title:
--   Section 3.4: exact zero-setup costs of the base-stock policies
-- statement:
--   Fix normalized lead-time demand $\mu\ge0$, penalty $a\ge0$ (unit demand rate, unit holding cost, no setup cost) and any demand environment of rate one. The empty no-order policy has average cost $a$, and for every integer level $j\ge1$ every policy following the base-stock rule ($r=j-1$, $Q=1$) has average cost
--   $$C_{\mu,a,0}(\pi_{\rm S}(j))=L_j(a)=H_j+a\,e_j=j-\mu+(\mu+a)\,e_j .$$
--
--   Pending replacements form an $M/D/j/j$ loss system, whose occupied-position count is Poisson$(\mu)$ conditioned to be at most $j$; $e_j$ is the long-run fraction of demand lost and $H_j$ the mean on-hand inventory. These closed forms are what the selection algorithm minimizes.
--
--   **Formalization Note** The average cost is the upper limit of expected average costs from the stated initialization ($j$ units on hand, empty pipeline), not a stationary expectation; the statement asserts that it equals the Erlang formula.
-- source:
--   M. Hu, "A 1.932 Guarantee for (r,Q) Policies in Continuous-Review Lost-Sales Inventory Systems", arXiv:2610.34576, 2026; Section 3.4, eq. (4) (p. 8); Section 3.2 (p. 6); Appendix A (p. A1).

import Definitions.Def_LostSalesRQ_model

namespace LostSalesRQ

theorem exact_base_stock_cost (μ a : ℝ) (hμ : 0 ≤ μ) (ha : 0 ≤ a) (S : DemandSpace 1) :
    (noOrderPolicy S).avgCost μ 1 a 0 = ENNReal.ofReal a ∧
    ∀ j : ℕ, 1 ≤ j → ∀ π : Policy S, IsRQPolicy μ (j - 1) 1 π →
      π.avgCost μ 1 a 0 = ENNReal.ofReal (baseStockCost μ a j) := by sorry

end LostSalesRQ

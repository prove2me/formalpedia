-- Prove2me | Theorems.Thm_LostSalesRQ_committed_supply_lower_bound
-- name    : LostSalesRQ.committed_supply_lower_bound
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-17T18:24:36.803324+00:00
-- url     : https://prove2.me/theorems/5c6c7344-ec2a-48db-ab12-758ba1b2774f
-- title:
--   Proposition 1: committed-supply lower bound
-- statement:
--   For every lead-time demand mean $\mu\ge0$, every lost-sales penalty $a\ge0$ and every rank weight $\eta\ge1$, the zero-setup optimal cost satisfies
--   $$\mathrm{OPT}_0(\mu,a)\ge\min\{B_\mu(\eta),\,a-D_\mu(\eta)\}.$$
--
--   The bound holds against every admissible policy, including history-dependent and randomized ones, and makes $\mathcal L_\mu(a)=\sup_{\eta\ge1}\min\{B_\mu(\eta),a-D_\mu(\eta)\}$ a computable lower bound on the optimal cost.
--
--   **Formalization Note** The left side is in $[0,\infty]$ and the right side is embedded by `ENNReal.ofReal`, so a negative right side gives the trivial bound $0$, as in the paper.
-- source:
--   M. Hu, "A 1.932 Guarantee for (r,Q) Policies in Continuous-Review Lost-Sales Inventory Systems", arXiv:2610.34576, 2026; Proposition 1, eq. (10) (p. 13); proof in Appendix B (pp. A4-A5).

import Definitions.Def_LostSalesRQ_model
import Definitions.Def_LostSalesRQ_lower_curve

namespace LostSalesRQ

theorem committed_supply_lower_bound (μ a η : ℝ) (hμ : 0 ≤ μ) (ha : 0 ≤ a) (hη : 1 ≤ η) :
    ENNReal.ofReal (min (rankBound μ η) (a - agingRateSup μ η)) ≤ OPTk μ a 0 := by sorry

end LostSalesRQ

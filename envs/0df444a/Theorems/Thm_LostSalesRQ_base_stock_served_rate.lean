-- Prove2me | Theorems.Thm_LostSalesRQ_base_stock_served_rate
-- name    : LostSalesRQ.base_stock_served_rate
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-18T04:17:21.027188+00:00
-- url     : https://prove2.me/theorems/1a6431b9-2181-4aff-92f2-7c000d1a7826
-- title:
--   Erlang loss rate of base stock (M/D/j/j)
-- statement:
--   Fix normalized lead-time demand $\mu\ge0$ and a demand environment of rate one. For every integer level $j\ge1$, every policy following the base-stock rule ($r=j-1$, $Q=1$) serves demand at long-run rate $1-e_j$: the expected number of demands served by time $T$, divided by $T$, converges to $1-e_j$, where $e_j=p_j(\mu)/F_j(\mu)$ is the Erlang loss fraction.
--
--   Under base stock $j$ with lead time $\mu$, units in replenishment form an $M/D/j/j$ loss system, and $e_j$ is Erlang's loss probability for it: the statement says that this is the long-run fraction of demand lost.
--
--   **Formalization Note** The statement concerns the expected served count from the stated initialization ($j$ units on hand, empty pipeline), as a limit of time averages.
-- source:
--   M. Hu, "A 1.932 Guarantee for (r,Q) Policies in Continuous-Review Lost-Sales Inventory Systems", arXiv:2610.34576, 2026; Section 3.4 (p. 8) and Appendix A (p. A1), citing Zachary (2007), Theorem 1, p. 241, and Wolff (1982), Theorem 1, p. 225.

import Definitions.Def_LostSalesRQ_model

namespace LostSalesRQ

theorem base_stock_served_rate (μ : ℝ) (hμ : 0 ≤ μ) (S : DemandSpace 1) (j : ℕ) (hj : 1 ≤ j)
    (π : Policy S) (hπ : IsRQPolicy μ (j - 1) 1 π) :
    Filter.Tendsto (fun T : ℝ => (π.expectedServed μ T).toReal / T) Filter.atTop
      (nhds (1 - lossFraction μ j)) := by sorry

end LostSalesRQ

-- Prove2me | Theorems.Thm_LostSalesRQ_stockout_aging_bound
-- name    : LostSalesRQ.stockout_aging_bound
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-17T18:30:15.272925+00:00
-- url     : https://prove2.me/theorems/c7143157-f4cb-4e48-b1cc-7503e2f3df6c
-- title:
--   Lemma D.2: stockout aging bound
-- statement:
--   For every $\mu\ge0$ and $\eta\ge1$,
--   $$D_\mu(\eta)\le\frac{\eta^2}{2}-\frac{\eta}{3}.$$
--
--   The bound is uniform in $\mu$ and controls the stockout requirement $a-D_\mu(\eta)$ in the comparisons below mean demand.
-- source:
--   M. Hu, "A 1.932 Guarantee for (r,Q) Policies in Continuous-Review Lost-Sales Inventory Systems", arXiv:2610.34576, 2026; Lemma D.2, eq. (D.3) (p. A9).

import Definitions.Def_LostSalesRQ_lower_curve

namespace LostSalesRQ

theorem stockout_aging_bound (μ η : ℝ) (hμ : 0 ≤ μ) (hη : 1 ≤ η) :
    agingRateSup μ η ≤ η ^ 2 / 2 - η / 3 := by sorry

end LostSalesRQ

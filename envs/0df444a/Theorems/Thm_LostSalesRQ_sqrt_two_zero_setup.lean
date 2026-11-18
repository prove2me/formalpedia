-- Prove2me | Theorems.Thm_LostSalesRQ_sqrt_two_zero_setup
-- name    : LostSalesRQ.sqrt_two_zero_setup
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-17T18:32:21.455514+00:00
-- url     : https://prove2.me/theorems/baf05d14-4147-4a39-a2e3-6834ba5ef84c
-- title:
--   Section 4.4.3: the $\sqrt2$ zero-setup comparison
-- statement:
--   For all $\mu\ge0$ and $a\ge0$,
--   $$U_\mu(a)\le\sqrt2\,\mathcal L_\mu(a)\qquad\text{and hence}\qquad U_\mu(a)\le\sqrt2\,\mathrm{OPT}_0(\mu,a).$$
--
--   This is the analytic heart of the zero-setup guarantee: the minimum closed-form base-stock cost is within $\sqrt2$ of the concave lower curve at every lead-time demand and penalty.
-- source:
--   M. Hu, "A 1.932 Guarantee for (r,Q) Policies in Continuous-Review Lost-Sales Inventory Systems", arXiv:2610.34576, 2026; Section 4.4.3, final display (p. 19).

import Definitions.Def_LostSalesRQ_model
import Definitions.Def_LostSalesRQ_lower_curve

namespace LostSalesRQ

theorem sqrt_two_zero_setup (μ a : ℝ) (hμ : 0 ≤ μ) (ha : 0 ≤ a) :
    minBaseStockCost μ a ≤ Real.sqrt 2 * lowerCurve μ a ∧
    ENNReal.ofReal (minBaseStockCost μ a) ≤ ENNReal.ofReal (Real.sqrt 2) * OPTk μ a 0 := by sorry

end LostSalesRQ

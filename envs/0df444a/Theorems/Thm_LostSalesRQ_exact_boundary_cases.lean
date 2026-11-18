-- Prove2me | Theorems.Thm_LostSalesRQ_exact_boundary_cases
-- name    : LostSalesRQ.exact_boundary_cases
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-17T18:29:44.828327+00:00
-- url     : https://prove2.me/theorems/bba9ff50-e45c-4998-897d-9d9cd60ae426
-- title:
--   Section 4.3.3: exact optimal cost for $a\le1$ and for $\mu=0$
-- statement:
--   1. If $\mu\ge0$ and $0\le a\le1$, then no replenishment is optimal and
--   $$\mathcal L_\mu(a)=\mathrm{OPT}_0(\mu,a)=U_\mu(a)=a .$$
--   2. If $\mu=0$ (immediate replenishment) and $a\ge0$, then
--   $$\mathcal L_0(a)=U_0(a)=\mathrm{OPT}_0(0,a)=\min\{a,1\}.$$
--
--   These boundary cases reduce the $\sqrt2$ comparison to $\mu>0$ and $a>1$, and the equality at $a=1$ starts the interval comparisons.
-- source:
--   M. Hu, "A 1.932 Guarantee for (r,Q) Policies in Continuous-Review Lost-Sales Inventory Systems", arXiv:2610.34576, 2026; Section 4.3.3, the two displays at the end of the subsection (p. 16).

import Definitions.Def_LostSalesRQ_model
import Definitions.Def_LostSalesRQ_lower_curve

namespace LostSalesRQ

theorem exact_boundary_cases :
    (∀ μ a : ℝ, 0 ≤ μ → 0 ≤ a → a ≤ 1 →
      lowerCurve μ a = a ∧ OPTk μ a 0 = ENNReal.ofReal a ∧ minBaseStockCost μ a = a) ∧
    (∀ a : ℝ, 0 ≤ a →
      lowerCurve 0 a = min a 1 ∧ minBaseStockCost 0 a = min a 1 ∧
        OPTk 0 a 0 = ENNReal.ofReal (min a 1)) := by sorry

end LostSalesRQ

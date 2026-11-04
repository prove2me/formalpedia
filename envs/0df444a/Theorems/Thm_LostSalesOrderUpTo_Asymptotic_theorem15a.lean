-- Prove2me | Theorems.Thm_LostSalesOrderUpTo_Asymptotic_theorem15a
-- name    : LostSalesOrderUpTo.Asymptotic.theorem15a
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T08:49:44.782586+00:00
-- url     : https://prove2.me/theorems/cb958f2a-74cf-407f-921e-6fcaa213bf62
-- title:
--   Theorem 15(a) — explicit finite-penalty policy bound
-- statement:
--   Let $\tau\ge1$, $h,b>0$, and let $S_{b+\tau h}$ and $S_{b/(\tau+1)}$ be the newsvendor levels for the lead-time demand at the indicated backorder penalties. If the expected holding quantity at $S_{b/(\tau+1)}$ is positive, then the lost-sales order-up-to policy satisfies
--
--   $$C^{\mathcal L,S_{b+\tau h}}(h,b)\le\frac{1+\nu_b\psi(S_{b/(\tau+1)};h,b/(\tau+1))}{1+\psi(S_{b/(\tau+1)};h,b/(\tau+1))}C^{\mathcal L*}(h,b),\qquad\nu_b=\frac{(b+\tau h)(\tau+1)}{b}.$$
--
--   The bound gives the paper's explicit performance factor at each finite penalty.
--
--   **Formalization Note** The multiplicative form avoids dividing by a zero optimal cost. The lost-sales comparator is the infimum over all admissible policies.
-- source:
--   Huh, Janakiraman, Muckstadt & Rusmevichientong, Asymptotic Optimality of Order-up-to Policies in Lost Sales Inventory Systems, working paper, December 4, 2006 (preprint of Management Science 55(3), 2009, DOI 10.1287/mnsc.1080.0945), p. 17, Theorem 15(a)

import Definitions.Def_LostSalesOrderUpTo_Asymptotic_Backorder

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators

namespace LostSalesOrderUpTo.Asymptotic

/-- Theorem 15(a), with the paper's exact finite-penalty factor. -/
theorem theorem15a (P : CappedBaseStock.DemandLaw)
    (c : CappedBaseStock.Parameters)
    (hhold : 0 < expectedHolding (leadTimeLaw P c.L)
      (newsvendorLevel (leadTimeLaw P c.L) c.h
        (c.p / ((c.L : ℝ) + 1)))) :
    CappedBaseStock.baseStockCost P c
      (newsvendorLevel (leadTimeLaw P c.L) c.h
        (c.p + (c.L : ℝ) * c.h)) ≤
    ENNReal.ofReal
      ((1 + ((c.p + (c.L : ℝ) * c.h) * ((c.L : ℝ) + 1) / c.p) *
        shortageHoldingRatio (leadTimeLaw P c.L) c.h
          (c.p / ((c.L : ℝ) + 1))
          (newsvendorLevel (leadTimeLaw P c.L) c.h
            (c.p / ((c.L : ℝ) + 1)))) /
       (1 + shortageHoldingRatio (leadTimeLaw P c.L) c.h
          (c.p / ((c.L : ℝ) + 1))
          (newsvendorLevel (leadTimeLaw P c.L) c.h
            (c.p / ((c.L : ℝ) + 1))))) * CappedBaseStock.OPT P c := by sorry

end LostSalesOrderUpTo.Asymptotic

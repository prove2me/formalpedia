-- Prove2me | Theorems.Thm_LostSalesOrderUpTo_Asymptotic_jss_lower_bound
-- name    : LostSalesOrderUpTo.Asymptotic.jss_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T08:49:18.579987+00:00
-- url     : https://prove2.me/theorems/46465cac-9fe0-43c7-a847-86897a632b92
-- title:
--   Janakiraman–Seshadri–Shanthikumar optimal-cost lower bound
-- statement:
--   Janakiraman, Seshadri and Shanthikumar (2005) compare the optimal costs of two canonical inventory systems. For lead time $\tau$, holding rate $h>0$, and lost-sales penalty $b>0$, their lower bound is
--
--   $$C^{\mathcal B*}\!\left(h,\frac{b}{\tau+1}\right)\le C^{\mathcal L*}(h,b).$$
--
--   The backorder optimum is over all order-up-to levels, while the lost-sales optimum is over all admissible policies. This lower bound supplies the comparator in Theorem 15.
--
--   **Formalization Note** The lost-sales optimum is an infimum over measurable, history-dependent, randomized policies; no optimal policy is assumed to exist.
-- source:
--   Huh, Janakiraman, Muckstadt & Rusmevichientong, Asymptotic Optimality of Order-up-to Policies in Lost Sales Inventory Systems, working paper, December 4, 2006 (preprint of Management Science 55(3), 2009, DOI 10.1287/mnsc.1080.0945), p. 13, §5, proof of Theorem 8 (bound of Janakiraman et al. 2005)

import Definitions.Def_LostSalesOrderUpTo_Asymptotic_Backorder

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators

namespace LostSalesOrderUpTo.Asymptotic

/-- The lower bound of Janakiraman, Seshadri and Shanthikumar (2005), quoted on p. 13. -/
theorem jss_lower_bound (P : CappedBaseStock.DemandLaw)
    (c : CappedBaseStock.Parameters) :
    ENNReal.ofReal (backorderOptimalCost (leadTimeLaw P c.L) c.h
        (c.p / ((c.L : ℝ) + 1))) ≤ CappedBaseStock.OPT P c := by sorry

end LostSalesOrderUpTo.Asymptotic

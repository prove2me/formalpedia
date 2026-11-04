-- Prove2me | Theorems.Thm_LostSalesOrderUpTo_Asymptotic_order_up_to_asymptotically_optimal
-- name    : LostSalesOrderUpTo.Asymptotic.order_up_to_asymptotically_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T08:49:48.005353+00:00
-- url     : https://prove2.me/theorems/8a7dd3a9-9b7f-46fc-8cb4-c999deca932b
-- title:
--   Theorem 15(b) — order-up-to asymptotic optimality
-- statement:
--   Let nonnegative i.i.d. single-period demand have finite positive mean, and let the lead time $\tau\ge1$ and holding rate $h>0$ be fixed. Suppose the sum $\mathbf D$ of $\tau+1$ demands satisfies Assumption 1. For every $\varepsilon>0$ there is $b_0>0$ such that, for every lost-sales penalty $b\ge b_0$,
--
--   $$\inf_{S\ge0}C^{\mathcal L,S}(h,b)\le C^{\mathcal L,S_{b+\tau h}}(h,b)\le(1+\varepsilon)C^{\mathcal L*}(h,b).$$
--
--   Here $S_{b+\tau h}$ is the newsvendor level for the backorder system with penalty $b+\tau h$. This is the paper's asymptotic optimality claim in a form that remains meaningful when both costs vanish.
--
--   **Formalization Note** $C^{\mathcal L*}$ is the infimum over all measurable, history-dependent, randomized policies. Lost-sales costs are extended nonnegative, and the infimum over $S$ replaces the paper's minimum without assuming attainment.
-- source:
--   Huh, Janakiraman, Muckstadt & Rusmevichientong, Asymptotic Optimality of Order-up-to Policies in Lost Sales Inventory Systems, working paper, December 4, 2006 (preprint of Management Science 55(3), 2009, DOI 10.1287/mnsc.1080.0945), p. 17, Theorem 15(b)

import Definitions.Def_LostSalesOrderUpTo_Asymptotic_Backorder

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators

namespace LostSalesOrderUpTo.Asymptotic

/-- Theorem 15(b), as an asymptotic multiplicative bound without a zero-cost ratio. -/
theorem order_up_to_asymptotically_optimal
    (P : CappedBaseStock.DemandLaw) (τ : ℕ) (h : ℝ)
    (hτ : 1 ≤ τ) (hh : 0 < h)
    (hassumption : AssumptionOne (leadTimeLaw P τ)) :
    ∀ ε : ℝ, 0 < ε → ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ c : CappedBaseStock.Parameters,
        c.L = τ → c.h = h → b₀ ≤ c.p →
          (⨅ S : ℝ≥0, CappedBaseStock.baseStockCost P c S) ≤
            CappedBaseStock.baseStockCost P c
              (newsvendorLevel (leadTimeLaw P τ) h
                (c.p + (τ : ℝ) * h)) ∧
          CappedBaseStock.baseStockCost P c
              (newsvendorLevel (leadTimeLaw P τ) h
                (c.p + (τ : ℝ) * h)) ≤
            ENNReal.ofReal (1 + ε) * CappedBaseStock.OPT P c := by sorry

end LostSalesOrderUpTo.Asymptotic

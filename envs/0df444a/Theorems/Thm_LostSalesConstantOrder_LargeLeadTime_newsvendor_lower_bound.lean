-- Prove2me | Theorems.Thm_LostSalesConstantOrder_LargeLeadTime_newsvendor_lower_bound
-- name    : LostSalesConstantOrder.LargeLeadTime.newsvendor_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T18:03:48.081065+00:00
-- url     : https://prove2.me/theorems/ec2afa41-93fb-4603-8eb7-8fc1ecd5db39
-- title:
--   Newsvendor bound: $\mathbb E[C^\pi_t]\ge g$ for every policy and period
-- statement:
--   In the lost-sales system with costs $h,c>0$ and demand law $\mathcal D$ (finite third moment, not deterministic), let $Q$ be the $c/(c+h)$ quantile of $\mathcal D$ and $g=h\mathbb E[(Q-D)^+]+c\mathbb E[(D-Q)^+]$ the optimal single-period newsvendor cost. For any admissible policy $\pi$ and any period $t$,
--   $$
--   \mathbb E[C^\pi_t]\ \ge\ g.
--   $$
--
--   It is the per-period lower bound that gives $\mathrm{OPT}(L,T)\ge Tg>0$ and turns the additive bound of Corollary 12 into the ratio bound of Theorem 1.
--
--   **Formalization Note** The period is any Lean period $t$ (the paper's $t+1$).
-- source:
--   Goldberg, Katz-Rogozhnikov, Lu, Sharma & Squillante, Asymptotic Optimality of Constant-Order Policies for Lost Sales Inventory Models with Large Lead Times, arXiv:1211.4063v2, p. 5, §3.1 (unnumbered display defining g)

import Definitions.Def_LostSalesConstantOrder_LargeLeadTime_Model

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace LostSalesConstantOrder.LargeLeadTime

/-- §3.1, p. 5 (unnumbered): for any policy `π` and any period `t`, `E[C_t^π] ≥ g`, where
`g = hE[(Q − D)^+] + cE[(D − Q)^+]` is the newsvendor cost at the `c/(c+h)` quantile `Q`. -/
theorem newsvendor_lower_bound (P : CappedBaseStock.DemandLaw) (prm : CappedBaseStock.Parameters)
    (h3 : FiniteThirdMoment P) (hnd : NonDeterministic P)
    (π : CappedBaseStock.AdmissiblePolicy) (t : ℕ) :
    ENNReal.ofReal (gConst P prm) ≤ periodExpectedCost P prm π t := by sorry

end LostSalesConstantOrder.LargeLeadTime

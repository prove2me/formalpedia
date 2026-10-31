-- Prove2me | Theorems.Thm_MinBuying_budget_characterization
-- name    : MinBuying.budget_characterization
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T16:21:04.768616+00:00
-- url     : https://prove2.me/theorems/2fc65436-d31c-49df-9235-c24a796de388
-- title:
--   Lemma 3 proof: cumulative-budget properties
-- statement:
--   The cumulative budget $A$ starts at zero, has the stated positive continuous derivative on $[0,1)$, satisfies $A\prime(x)(1-x)^2\le1-x$, and is a strictly increasing bijection from $[0,1)$ onto the nonnegative reals.
-- source:
--   Titing Cui, Michael L. Hamilton, Jourdain Lamperski, and Kasra Ganjizadeh Tari, Unit-Demand Pricing for Min-Buying Customers, September 27, 2026 manuscript, 47 PDF pages (main pp.1–27; companion ec1–ec20). https://doi.org/10.2139/ssrn.5178133 . PDF pp.38–42/ec11–ec15, proof of Lemma 3.

import Definitions.Def_MinBuying_Analytic

open Set

namespace MinBuying

theorem budget_characterization :
    canonicalBudget 0 = 0 ∧
    ContinuousOn budgetSlope (Ico (0 : ℝ) 1) ∧
    (∀ x ∈ Ico (0 : ℝ) 1,
      HasDerivWithinAt canonicalBudget (budgetSlope x) (Ico (0 : ℝ) 1) x ∧
      0 < budgetSlope x ∧ budgetSlope x * (1 - x) ^ 2 ≤ 1 - x) ∧
    StrictMonoOn canonicalBudget (Ico (0 : ℝ) 1) ∧
    (∀ s : ℝ, 0 ≤ s → ∃! x : ℝ, x ∈ Ico (0 : ℝ) 1 ∧ canonicalBudget x = s) := by
  sorry

end MinBuying

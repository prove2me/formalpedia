-- Prove2me | Theorems.Thm_MinBuying_benchmark_characterization
-- name    : MinBuying.benchmark_characterization
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T16:21:28.210644+00:00
-- url     : https://prove2.me/theorems/a4aae849-b8b5-4948-a597-222124c43348
-- title:
--   Equation (10): existence and uniqueness of the concrete benchmark
-- statement:
--   The explicitly defined integral benchmark satisfies $c(0)=1$, is continuous on $[0,1)$, solves $c\prime(x)=A\prime(x)(1-xc(x))$ on $(0,1)$, and is the unique continuous solution with this initial condition.
-- source:
--   Titing Cui, Michael L. Hamilton, Jourdain Lamperski, and Kasra Ganjizadeh Tari, Unit-Demand Pricing for Min-Buying Customers, September 27, 2026 manuscript, 47 PDF pages (main pp.1–27; companion ec1–ec20). https://doi.org/10.2139/ssrn.5178133 . p.17 Eq.(10); PDF pp.39–42/ec12–ec15.

import Definitions.Def_MinBuying_Analytic

open Set

namespace MinBuying

theorem benchmark_characterization :
    continuousBenchmark 0 = 1 ∧
    ContinuousOn continuousBenchmark (Ico (0 : ℝ) 1) ∧
    (∀ x ∈ Ioo (0 : ℝ) 1,
      HasDerivAt continuousBenchmark
        (budgetSlope x * (1 - x * continuousBenchmark x)) x) ∧
    (∀ f : ℝ → ℝ, f 0 = 1 → ContinuousOn f (Ico (0 : ℝ) 1) →
      (∀ x ∈ Ioo (0 : ℝ) 1,
        HasDerivAt f (budgetSlope x * (1 - x * f x)) x) →
      EqOn f continuousBenchmark (Ico (0 : ℝ) 1)) := by
  sorry

end MinBuying

-- Prove2me | Theorems.Thm_MinBuying_critical_ratio_characterization
-- name    : MinBuying.critical_ratio_characterization
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T16:21:50.630076+00:00
-- url     : https://prove2.me/theorems/4b6443d4-4eea-4243-8468-f3c5995efb58
-- title:
--   Lemma 3 proof: unique critical ratio and benchmark maximum
-- statement:
--   The exact critical ratio lies strictly between zero and one and is the unique root of $xc(x)=1$ there. On $[0,1)$, $1\le c(x)\le1/x^\star$. The benchmark is strictly increasing up to $x^\star$ and strictly decreasing afterward. These are conclusions about the concrete integral definition, not assumptions about an arbitrary function.
-- source:
--   Titing Cui, Michael L. Hamilton, Jourdain Lamperski, and Kasra Ganjizadeh Tari, Unit-Demand Pricing for Min-Buying Customers, September 27, 2026 manuscript, 47 PDF pages (main pp.1–27; companion ec1–ec20). https://doi.org/10.2139/ssrn.5178133 . PDF pp.39–42/ec12–ec15, including Eq.(EC.18).

import Definitions.Def_MinBuying_Analytic

open Set

namespace MinBuying

theorem critical_ratio_characterization :
    criticalRatio ∈ Ioo (0 : ℝ) 1 ∧
    criticalRatio * continuousBenchmark criticalRatio = 1 ∧
    (∀ x ∈ Ioo (0 : ℝ) 1,
      x * continuousBenchmark x = 1 → x = criticalRatio) ∧
    (∀ x ∈ Ico (0 : ℝ) 1,
      1 ≤ continuousBenchmark x ∧ continuousBenchmark x ≤ 1 / criticalRatio) ∧
    StrictMonoOn continuousBenchmark (Icc (0 : ℝ) criticalRatio) ∧
    StrictAntiOn continuousBenchmark (Ico criticalRatio 1) := by
  sorry

end MinBuying

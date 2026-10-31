-- Prove2me | Theorems.Thm_MinBuying_theorem4_regular_tight
-- name    : MinBuying.theorem4_regular_tight
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T16:27:26.063935+00:00
-- url     : https://prove2.me/theorems/be7bf237-adaa-4ce7-9fd9-6c009afcad13
-- title:
--   Theorem 4: the exact tight guarantee for independent regular valuations
-- statement:
--   The exact constant $x^\star$ is the unique root of $xc(x)=1$ in $(0,1)$ for the explicitly defined benchmark. Every independent continuous regular instance with the source's finite attained positive-optimum conditions satisfies $R_{\mathrm{UP}}\ge x^\star R_{\mathrm{DP}}$. For every $\varepsilon>0$, some positive finite item count and such an instance satisfy $R_{\mathrm{DP}}/R_{\mathrm{UP}}>1/x^\star-\varepsilon$. Thus the universal factor is tight across finite instances. The decimal $0.6986$ is not part of the formal statement.
-- source:
--   Titing Cui, Michael L. Hamilton, Jourdain Lamperski, and Kasra Ganjizadeh Tari, Unit-Demand Pricing for Min-Buying Customers, September 27, 2026 manuscript, 47 PDF pages (main pp.1–27; companion ec1–ec20). https://doi.org/10.2139/ssrn.5178133 . p.17, Theorem 4 and Eq.(10); tightness discussion p.23.

import Definitions.Def_MinBuying_Regularity
import Definitions.Def_MinBuying_Analytic

open MeasureTheory Set

namespace MinBuying

/-- Theorem 4, including both the universal guarantee and sharpness over
finite item counts. The exact root is characterized explicitly to protect
against any default value of the infimum used in its definition. -/
theorem theorem4_regular_tight :
    criticalRatio ∈ Ioo (0 : ℝ) 1 ∧
    criticalRatio * continuousBenchmark criticalRatio = 1 ∧
    (∀ x ∈ Ioo (0 : ℝ) 1,
      x * continuousBenchmark x = 1 → x = criticalRatio) ∧
    (∀ (n : ℕ) (F : Fin n → Measure ℝ), RegularInstance F →
      criticalRatio * DPRevenue (productLaw F) ≤ UPRevenue (productLaw F)) ∧
    (∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (F : Fin n → Measure ℝ),
      RegularInstance F ∧
      1 / criticalRatio - ε < DPRevenue (productLaw F) / UPRevenue (productLaw F)) := by
  sorry

end MinBuying

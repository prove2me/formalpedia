-- Prove2me | Theorems.Thm_Freiman_gap_lower_application
-- name    : Freiman.gap_lower_application
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:14:22.058572+00:00
-- url     : https://prove2.me/theorems/dd36d2e2-532e-41bc-b3e5-6b3e0bce180a
-- title:
--   gap lower application
-- statement:
--   Apply the certified rows successively by finite induction; reflection is included and earlier exclusions are established before use.
-- source:
--   Freiman Hall ray report, m3.tex; lem:m3:tables

import Definitions.Def_Freiman_gapCertificateData

namespace Freiman

theorem gap_lower_application (hsound : GapCertificateSoundness) (hb : gapLowerRows.length = 19 ∧ gapLowerTrees.length = 19 ∧ ∀ n : ℕ, n < 19 → gapRoot (gapLowerTrees[n]!) = (gapLowerRows[n]!).state) (hcoverage : ∀ tree ∈ gapLowerTrees, gapCoverage tree) (hchecks : ∀ n : ℕ, n < 19 → gapChecks (gapLowerRows.take n) [] .forbidden (gapLowerTrees[n]!)) (a : ℤ → ℕ+) (hd : gapDigits a) (hc : gapCapped a) : gapLowerValid a gapLowerRows := by
  sorry

end Freiman

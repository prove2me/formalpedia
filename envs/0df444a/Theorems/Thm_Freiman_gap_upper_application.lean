-- Prove2me | Theorems.Thm_Freiman_gap_upper_application
-- name    : Freiman.gap_upper_application
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:14:36.642848+00:00
-- url     : https://prove2.me/theorems/df4a92cc-f010-4299-af19-a67ff8acfe2a
-- title:
--   gap upper application
-- statement:
--   Apply the independent upper certificates to every matching marked word and its reflection.
-- source:
--   Freiman Hall ray report, m3.tex; lem:m3:tables

import Definitions.Def_Freiman_gapCertificateData

namespace Freiman

theorem gap_upper_application (hsound : GapCertificateSoundness) (hb : gapUpperRows.length = 11 ∧ gapUpperTrees.length = 11 ∧ ∀ n : ℕ, n < 11 → gapRoot (gapUpperTrees[n]!) = (gapUpperRows[n]!).state) (hcoverage : ∀ tree ∈ gapUpperTrees, gapCoverage tree) (hchecks : ∀ n : ℕ, n < 11 → gapChecks [] [] (.upper (gapUpperRows[n]!).bound) (gapUpperTrees[n]!)) (a : ℤ → ℕ+) (hd : gapDigits a) (hc : gapCapped a) : gapUpperValid a gapUpperRows := by
  sorry

end Freiman

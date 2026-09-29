-- Prove2me | Theorems.Thm_Freiman_gap_upper_checks
-- name    : Freiman.gap_upper_checks
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:14:31.827564+00:00
-- url     : https://prove2.me/theorems/76bbe923-a970-4af2-8cf2-5d330d4d2825
-- title:
--   gap upper checks
-- statement:
--   All upper rows are checked without assumptions from either table.
-- source:
--   Freiman Hall ray report, m3.tex; lem:m3:tables

import Definitions.Def_Freiman_gapCertificateData

namespace Freiman

theorem gap_upper_checks : ∀ n : ℕ, n < 11 → gapChecks [] [] (.upper (gapUpperRows[n]!).bound) (gapUpperTrees[n]!) := by
  sorry

end Freiman

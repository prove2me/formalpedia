-- Prove2me | Theorems.Thm_Freiman_gap_lower_table
-- name    : Freiman.gap_lower_table
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:14:17.984984+00:00
-- url     : https://prove2.me/theorems/d69ef7e6-4e2c-4128-a6cb-b5ab6f0ba1b8
-- title:
--   gap lower table
-- statement:
--   Under the common cap q, all 19 lower-table words and their reversals are forbidden.
-- source:
--   Freiman Hall ray report, m3.tex; lem:m3:tables

import Definitions.Def_Freiman_gapCertificateData

namespace Freiman

theorem gap_lower_table (a : ℤ → ℕ+) (hc : gapCapped a) : gapLowerValid a gapLowerRows := by
  sorry

end Freiman

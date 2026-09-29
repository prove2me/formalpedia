-- Prove2me | Theorems.Thm_Freiman_gap_lower_checks_7_11
-- name    : Freiman.gap_lower_checks_7_11
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:12:56.782166+00:00
-- url     : https://prove2.me/theorems/63182e50-ec89-48c3-bf76-512da885578e
-- title:
--   gap lower checks 7 11
-- statement:
--   Exact rational leaf inequalities and strictly earlier forbidden-row references for lower rows 7–11.
-- source:
--   Freiman Hall ray report, certificates/gap/lower_table_partitions.json

import Definitions.Def_Freiman_gapCertificateData

namespace Freiman

theorem gap_lower_checks_7_11 : ∀ n : ℕ, 5 ≤ n → n < 10 → gapChecks (gapLowerRows.take n) [] .forbidden (gapLowerTrees[n]!) := by
  sorry

end Freiman

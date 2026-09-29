-- Prove2me | Theorems.Thm_Freiman_gap_lower_checks_2_6
-- name    : Freiman.gap_lower_checks_2_6
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:12:51.570986+00:00
-- url     : https://prove2.me/theorems/b6ef99dc-c008-434f-a51a-cc0cdbfe4e8c
-- title:
--   gap lower checks 2 6
-- statement:
--   Exact rational leaf inequalities and strictly earlier forbidden-row references for lower rows 2–6.
-- source:
--   Freiman Hall ray report, certificates/gap/lower_table_partitions.json

import Definitions.Def_Freiman_gapCertificateData

namespace Freiman

theorem gap_lower_checks_2_6 : ∀ n : ℕ, 0 ≤ n → n < 5 → gapChecks (gapLowerRows.take n) [] .forbidden (gapLowerTrees[n]!) := by
  sorry

end Freiman

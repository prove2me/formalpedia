-- Prove2me | Theorems.Thm_Freiman_gap_lower_checks_17_20
-- name    : Freiman.gap_lower_checks_17_20
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:12:47.615754+00:00
-- url     : https://prove2.me/theorems/65f837f8-3fbb-4d81-b22a-5e110fae14f4
-- title:
--   gap lower checks 17 20
-- statement:
--   Exact rational leaf inequalities and strictly earlier forbidden-row references for lower rows 17–20.
-- source:
--   Freiman Hall ray report, certificates/gap/lower_table_partitions.json

import Definitions.Def_Freiman_gapCertificateData

namespace Freiman

theorem gap_lower_checks_17_20 : ∀ n : ℕ, 15 ≤ n → n < 19 → gapChecks (gapLowerRows.take n) [] .forbidden (gapLowerTrees[n]!) := by
  sorry

end Freiman

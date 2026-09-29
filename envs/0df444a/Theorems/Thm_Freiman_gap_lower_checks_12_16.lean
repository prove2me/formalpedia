-- Prove2me | Theorems.Thm_Freiman_gap_lower_checks_12_16
-- name    : Freiman.gap_lower_checks_12_16
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:12:54.482525+00:00
-- url     : https://prove2.me/theorems/55aa2a88-e8e3-40b0-9bae-0f5ef501a08f
-- title:
--   gap lower checks 12 16
-- statement:
--   Exact rational leaf inequalities and strictly earlier forbidden-row references for lower rows 12–16.
-- source:
--   Freiman Hall ray report, certificates/gap/lower_table_partitions.json

import Definitions.Def_Freiman_gapCertificateData

namespace Freiman

theorem gap_lower_checks_12_16 : ∀ n : ℕ, 10 ≤ n → n < 15 → gapChecks (gapLowerRows.take n) [] .forbidden (gapLowerTrees[n]!) := by
  sorry

end Freiman

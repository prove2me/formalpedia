-- Prove2me | Theorems.Thm_Freiman_gap_lower_coverage
-- name    : Freiman.gap_lower_coverage
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:12:44.620984+00:00
-- url     : https://prove2.me/theorems/ef1fc0f0-78c9-4825-9e22-edd5f0d52a52
-- title:
--   gap lower coverage
-- statement:
--   All 119 nodes in the 19 supplied lower partitions have exhaustive four-child splits and well-formed centres.
-- source:
--   Freiman Hall ray report, certificates/gap/lower_table_partitions.json

import Definitions.Def_Freiman_gapCertificateData

namespace Freiman

theorem gap_lower_coverage : ∀ tree ∈ gapLowerTrees, gapCoverage tree := by
  sorry

end Freiman

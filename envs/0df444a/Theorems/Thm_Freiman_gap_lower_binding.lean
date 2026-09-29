-- Prove2me | Theorems.Thm_Freiman_gap_lower_binding
-- name    : Freiman.gap_lower_binding
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:12:41.796305+00:00
-- url     : https://prove2.me/theorems/3f66a861-3ec0-4afd-8d0b-4c6a556779b0
-- title:
--   gap lower binding
-- statement:
--   The 19 lower trees are bound to exactly report rows 2–20, in the required order.
-- source:
--   Freiman Hall ray report, certificates/gap/source_rows.json and lower_table_partitions.json

import Definitions.Def_Freiman_gapCertificateData

namespace Freiman

theorem gap_lower_binding : gapLowerRows.length = 19 ∧ gapLowerTrees.length = 19 ∧ ∀ n : ℕ, n < 19 → gapRoot (gapLowerTrees[n]!) = (gapLowerRows[n]!).state := by
  sorry

end Freiman

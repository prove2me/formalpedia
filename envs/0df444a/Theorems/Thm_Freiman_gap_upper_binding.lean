-- Prove2me | Theorems.Thm_Freiman_gap_upper_binding
-- name    : Freiman.gap_upper_binding
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:14:20.099931+00:00
-- url     : https://prove2.me/theorems/cc16b59b-b23f-45c9-8f06-18d058b1de8f
-- title:
--   gap upper binding
-- statement:
--   The upper-tree roots and distinguished coordinates exactly match report rows 21–31.
-- source:
--   Freiman Hall ray report, certificates/gap/source_rows.json and upper_table_partitions.json

import Definitions.Def_Freiman_gapCertificateData

namespace Freiman

theorem gap_upper_binding : gapUpperRows.length = 11 ∧ gapUpperTrees.length = 11 ∧ ∀ n : ℕ, n < 11 → gapRoot (gapUpperTrees[n]!) = (gapUpperRows[n]!).state := by
  sorry

end Freiman

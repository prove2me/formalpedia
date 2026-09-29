-- Prove2me | Theorems.Thm_Freiman_gap_upper_checks_25_28
-- name    : Freiman.gap_upper_checks_25_28
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:14:22.914979+00:00
-- url     : https://prove2.me/theorems/2ac2dd27-939d-4098-864d-31a2a9b9adb5
-- title:
--   gap upper checks 25 28
-- statement:
--   Exact upper-cylinder and cap contradiction leaf checks for rows 25–28, with no lower-row exclusions assumed.
-- source:
--   Freiman Hall ray report, certificates/gap/upper_table_partitions.json

import Definitions.Def_Freiman_gapCertificateData

namespace Freiman

theorem gap_upper_checks_25_28 : ∀ n : ℕ, 4 ≤ n → n < 8 → gapChecks [] [] (.upper (gapUpperRows[n]!).bound) (gapUpperTrees[n]!) := by
  sorry

end Freiman

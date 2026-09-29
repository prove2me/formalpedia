-- Prove2me | Theorems.Thm_Freiman_gap_upper_checks_21_24
-- name    : Freiman.gap_upper_checks_21_24
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:14:25.406726+00:00
-- url     : https://prove2.me/theorems/6f78319d-65a6-4535-a13c-a507f6e0e4a6
-- title:
--   gap upper checks 21 24
-- statement:
--   Exact upper-cylinder and cap contradiction leaf checks for rows 21–24, with no lower-row exclusions assumed.
-- source:
--   Freiman Hall ray report, certificates/gap/upper_table_partitions.json

import Definitions.Def_Freiman_gapCertificateData

namespace Freiman

theorem gap_upper_checks_21_24 : ∀ n : ℕ, 0 ≤ n → n < 4 → gapChecks [] [] (.upper (gapUpperRows[n]!).bound) (gapUpperTrees[n]!) := by
  sorry

end Freiman

-- Prove2me | Theorems.Thm_Freiman_gap_upper_checks_29_31
-- name    : Freiman.gap_upper_checks_29_31
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:14:29.00429+00:00
-- url     : https://prove2.me/theorems/34e2a3c0-b5ac-45db-8f14-e696fcd6bd79
-- title:
--   gap upper checks 29 31
-- statement:
--   Exact upper-cylinder and cap contradiction leaf checks for rows 29–31, with no lower-row exclusions assumed.
-- source:
--   Freiman Hall ray report, certificates/gap/upper_table_partitions.json

import Definitions.Def_Freiman_gapCertificateData

namespace Freiman

theorem gap_upper_checks_29_31 : ∀ n : ℕ, 8 ≤ n → n < 11 → gapChecks [] [] (.upper (gapUpperRows[n]!).bound) (gapUpperTrees[n]!) := by
  sorry

end Freiman

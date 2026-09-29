-- Prove2me | Theorems.Thm_Freiman_gap_maximum_admissible
-- name    : Freiman.gap_maximum_admissible
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:17:15.39132+00:00
-- url     : https://prove2.me/theorems/0f6db923-ea9f-4e93-8f5c-4c3f4935e27f
-- title:
--   gap maximum admissible
-- statement:
--   Collect exactly the admissibility conditions used by the maximizing first-difference tables.
-- source:
--   Freiman Hall ray report, m3_maximum.tex

import Definitions.Def_Freiman_gapModel

namespace Freiman

theorem gap_maximum_admissible (a : ℤ → ℕ+) (hc : gapCapped a) : gapMaximumAdmissible a := by
  sorry

end Freiman

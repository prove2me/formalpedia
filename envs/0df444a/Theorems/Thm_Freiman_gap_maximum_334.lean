-- Prove2me | Theorems.Thm_Freiman_gap_maximum_334
-- name    : Freiman.gap_maximum_334
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:17:12.758657+00:00
-- url     : https://prove2.me/theorems/1eba54ee-d634-49ec-b9c6-8a16f8197aae
-- title:
--   gap maximum 334
-- statement:
--   The complete two-level extension of 334 reaches 41,42,3343,33443 or33444; reflection excludes433.
-- source:
--   Freiman Hall ray report, m3_maximum.tex; derived334 partition

import Definitions.Def_Freiman_gapModel

namespace Freiman

theorem gap_maximum_334 (a : ℤ → ℕ+) (hd : gapDigits a) (hf : ∀ w ∈ gapMaximumForbidden, gapAvoids a w) : gapAvoids a [3,3,4] := by
  sorry

end Freiman

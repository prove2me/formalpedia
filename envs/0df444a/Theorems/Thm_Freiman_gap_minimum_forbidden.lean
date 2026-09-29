-- Prove2me | Theorems.Thm_Freiman_gap_minimum_forbidden
-- name    : Freiman.gap_minimum_forbidden
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:17:10.004995+00:00
-- url     : https://prove2.me/theorems/ea81016c-6117-4a76-a588-a7587f81db06
-- title:
--   gap minimum forbidden
-- statement:
--   All minimum forbidden words and reversals are excluded under the global cap.
-- source:
--   Freiman Hall ray report, m3_minimum.tex

import Definitions.Def_Freiman_gapModel

namespace Freiman

theorem gap_minimum_forbidden (a : ℤ → ℕ+) (hc : gapCapped a) : ∀ w ∈ gapMinimumForbidden, gapAvoids a w := by
  sorry

end Freiman

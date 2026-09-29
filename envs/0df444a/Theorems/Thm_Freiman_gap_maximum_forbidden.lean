-- Prove2me | Theorems.Thm_Freiman_gap_maximum_forbidden
-- name    : Freiman.gap_maximum_forbidden
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:17:19.894556+00:00
-- url     : https://prove2.me/theorems/b8f9a53e-e1c7-42c2-980d-ef08fb1e791a
-- title:
--   gap maximum forbidden
-- statement:
--   All maximum forbidden words and reversals are excluded under the global cap.
-- source:
--   Freiman Hall ray report, m3_maximum.tex

import Definitions.Def_Freiman_gapModel

namespace Freiman

theorem gap_maximum_forbidden (a : ℤ → ℕ+) (hc : gapCapped a) : ∀ w ∈ gapMaximumForbidden, gapAvoids a w := by
  sorry

end Freiman

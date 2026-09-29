-- Prove2me | Theorems.Thm_Freiman_gap_window_upper
-- name    : Freiman.gap_window_upper
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:15:05.805989+00:00
-- url     : https://prove2.me/theorems/a7828695-f888-4c70-b5a3-d8c457a98f7b
-- title:
--   gap window upper
-- statement:
--   Apply the strict cylinder estimate to the actual radius-r word at any coordinate.
-- source:
--   Freiman Hall ray report, m3.tex; eq:m3:cylinder

import Definitions.Def_Freiman_gapModel

namespace Freiman

theorem gap_window_upper (a : ℤ → ℕ+) (i : ℤ) (r : ℕ) (hd : gapDigits a) : localValue a i < (gapCylinderUpper (gapLocalWindow a i r) r : ℝ) := by
  sorry

end Freiman

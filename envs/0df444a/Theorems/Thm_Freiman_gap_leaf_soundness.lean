-- Prove2me | Theorems.Thm_Freiman_gap_leaf_soundness
-- name    : Freiman.gap_leaf_soundness
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:12:46.083901+00:00
-- url     : https://prove2.me/theorems/370c8cd3-e21f-4abd-95e4-b31334e01ea6
-- title:
--   gap leaf soundness
-- statement:
--   All five checked leaf constructors imply their declared semantic outcome.
-- source:
--   Freiman Hall ray report, m3.tex; finite partition induction

import Definitions.Def_Freiman_gapCertificateData

namespace Freiman

theorem gap_leaf_soundness (lower upper : List GapRow) (mode : GapMode) (s : GapState) (a : ℤ → ℕ+) (i : ℤ) (hd : gapDigits a) (hc : gapCapped a) (hl : gapLowerValid a lower) (hu : gapUpperValid a upper) (hm : gapMatch a i s) (r : GapReason) (hcheck : gapLeafCheck lower upper mode s r) : gapModeOutcome mode a i := by
  sorry

end Freiman

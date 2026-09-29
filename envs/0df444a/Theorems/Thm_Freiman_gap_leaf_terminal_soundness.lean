-- Prove2me | Theorems.Thm_Freiman_gap_leaf_terminal_soundness
-- name    : Freiman.gap_leaf_terminal_soundness
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:17:46.673984+00:00
-- url     : https://prove2.me/theorems/d5fe2d65-f6c5-45e6-b52a-bd1ac3fd9b4e
-- title:
--   gap leaf terminal soundness
-- statement:
--   Each terminal certificate is aligned exactly with A, B, or its reflection, so the original marked coordinate is preserved.
-- source:
--   Freiman Hall ray report, m3.tex; lem:m3:tree

import Definitions.Def_Freiman_gapCertificate

namespace Freiman

theorem gap_leaf_terminal_soundness (lower upper : List GapRow) (mode : GapMode) (s : GapState) (a : ℤ → ℕ+) (i : ℤ) (hd : gapDigits a) (hc : gapCapped a) (hl : gapLowerValid a lower) (hu : gapUpperValid a upper) (hm : gapMatch a i s) (hcheck : gapLeafCheck lower upper mode s .terminal) : gapModeOutcome mode a i := by
  sorry

end Freiman

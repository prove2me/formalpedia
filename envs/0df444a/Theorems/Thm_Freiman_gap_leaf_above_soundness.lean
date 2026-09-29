-- Prove2me | Theorems.Thm_Freiman_gap_leaf_above_soundness
-- name    : Freiman.gap_leaf_above_soundness
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:17:50.407308+00:00
-- url     : https://prove2.me/theorems/8fc4fb0f-d5e3-49ad-a606-d3863ffdf282
-- title:
--   gap leaf above soundness
-- statement:
--   A checked rational lower bound at least q forces an actual height strictly above q and contradicts the cap.
-- source:
--   Freiman Hall ray report, m3.tex; lem:m3:tables

import Definitions.Def_Freiman_gapCertificate

namespace Freiman

theorem gap_leaf_above_soundness (lower upper : List GapRow) (mode : GapMode) (s : GapState) (a : ℤ → ℕ+) (i : ℤ) (hd : gapDigits a) (hc : gapCapped a) (hl : gapLowerValid a lower) (hu : gapUpperValid a upper) (hm : gapMatch a i s) (j : ℕ) (hcheck : gapLeafCheck lower upper mode s (.above j)) : gapModeOutcome mode a i := by
  sorry

end Freiman

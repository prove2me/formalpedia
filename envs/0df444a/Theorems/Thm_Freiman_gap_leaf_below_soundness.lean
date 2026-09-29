-- Prove2me | Theorems.Thm_Freiman_gap_leaf_below_soundness
-- name    : Freiman.gap_leaf_below_soundness
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:12:36.115981+00:00
-- url     : https://prove2.me/theorems/e5df70a3-a7c2-48c3-ab02-63146fd7b31c
-- title:
--   gap leaf below soundness
-- statement:
--   Soundness of the below leaf rule: finite data is interpreted using actual local heights, prior exclusions, and marked-coordinate alignment.
-- source:
--   Freiman Hall ray report, m3.tex; lem:m3:tables and lem:m3:tree

import Definitions.Def_Freiman_gapCertificateData

namespace Freiman

theorem gap_leaf_below_soundness (lower upper : List GapRow) (mode : GapMode) (s : GapState) (a : ℤ → ℕ+) (i : ℤ) (hd : gapDigits a) (hc : gapCapped a) (hl : gapLowerValid a lower) (hu : gapUpperValid a upper) (hm : gapMatch a i s)  (hcheck : gapLeafCheck lower upper mode s (.below)) : gapModeOutcome mode a i := by
  sorry

end Freiman

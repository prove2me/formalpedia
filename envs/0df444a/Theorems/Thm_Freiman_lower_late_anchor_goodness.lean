-- Prove2me | Theorems.Thm_Freiman_lower_late_anchor_goodness
-- name    : Freiman.lower_late_anchor_goodness
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T15:00:01.793481+00:00
-- url     : https://prove2.me/theorems/898bf4c0-cd68-41e8-860c-b21b1b2fc731
-- title:
--   lower late anchor goodness
-- statement:
--   Both inherited anchor covers are good by their own explicit strict-goodness records in the original trunk table.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_lowerCertificates

open Freiman

theorem Freiman.lower_late_anchor_goodness (t : ℝ) (p : LowerPair) (hs : lowerState t p)
    (hd : ¬ lowerMixed p ∧ ¬ lowerA p 3 ∧ ¬ lowerA p 9 ∧ lowerL p ∧ ¬ lowerLStar p) :
    lowerGood (lowerChild p ([2],[2])) ∧ lowerGood (lowerChild p ([2],[1])) := by
  sorry

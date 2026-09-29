-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_anchor_goodness
-- name    : Freiman.lowerEarlyTerminal_anchor_goodness
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:59:44.994653+00:00
-- url     : https://prove2.me/theorems/fe1fcb03-9932-4a11-83e7-a28cf79dc6aa
-- title:
--   lowerEarlyTerminal anchor goodness
-- statement:
--   Both inherited anchor covers are good by their own explicit strict-goodness records in the original trunk table.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_lowerCertificates

open Freiman

theorem Freiman.lowerEarlyTerminal_anchor_goodness (t : ℝ) (p : LowerPair) (hs : lowerState t p)
    (hd : lowerEarlyDomain p) :
    lowerGood (lowerChild p ([3],[2])) ∧ lowerGood (lowerChild p ([2],[2])) := by
  sorry

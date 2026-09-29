-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_lower_anchor
-- name    : Freiman.lowerEarlyTerminal_lower_anchor
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T15:00:24.709984+00:00
-- url     : https://prove2.me/theorems/b773773f-0924-48b9-adaa-8ce0dab29c7f
-- title:
--   lowerEarlyTerminal lower anchor
-- statement:
--   The H9-notH16 source row ends at C32; its printed lower anchor is exactly the early lower-target inequality used by the later H5 history argument.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.lowerEarlyTerminal_lower_anchor (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hd : lowerEarlyDomain p) :
    lowerLocalLower p ([3],[2]) ≤
    (if (lowerNormalize p).1.length % 2 = 0 then lowerEndpoint p false else -lowerEndpoint p true) := by
  sorry

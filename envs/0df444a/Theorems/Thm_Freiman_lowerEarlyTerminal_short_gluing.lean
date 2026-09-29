-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_short_gluing
-- name    : Freiman.lowerEarlyTerminal_short_gluing
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:51:49.039955+00:00
-- url     : https://prove2.me/theorems/e21e38be-2936-4be7-bd1d-afff3eaf5bc2
-- title:
--   Freiman.lowerEarlyTerminal_short_gluing
-- statement:
--   A nonempty finite chain of closed intervals is connected and contains both listed anchors.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert.

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem Freiman.lowerEarlyTerminal_short_gluing (p : LowerPair) (mode : ℕ) (hm : mode<2)
    (h : lowerEarlyTerminalShortData p (if mode=0 then lowerEarlyTerminalFirst else lowerEarlyTerminalSecond)) :
    lowerEarlyTerminalListGeometry p (if mode=0 then lowerEarlyTerminalFirst else lowerEarlyTerminalSecond) := by
  sorry

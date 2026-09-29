-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_terminal_gluing
-- name    : Freiman.lowerEarlyTerminal_terminal_gluing
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:51:10.0238+00:00
-- url     : https://prove2.me/theorems/853c392e-4e05-4bc5-8ad7-569fd7c95026
-- title:
--   Freiman.lowerEarlyTerminal_terminal_gluing
-- statement:
--   The exact finite interval graph is connected, including the A46 alternative and the two-interval terminal cluster; both anchors are listed.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert.

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem Freiman.lowerEarlyTerminal_terminal_gluing (p : LowerPair) (primary : Bool) (h : lowerEarlyTerminalTerminalData p primary) :
    lowerEarlyTerminalListGeometry p (lowerEarlyTerminalTerminal primary) := by
  sorry

-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_terminal_geometry
-- name    : Freiman.lowerEarlyTerminal_terminal_geometry
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:51:46.213149+00:00
-- url     : https://prove2.me/theorems/affd4b38-bdd4-40e0-a69d-f0a34f0dac47
-- title:
--   Freiman.lowerEarlyTerminal_terminal_geometry
-- statement:
--   Assemble all terminal source requirements and the exact finite interval graph.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert.

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem Freiman.lowerEarlyTerminal_terminal_geometry (C : LowerEarlyTerminalCatalog) (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hd : lowerEarlyDomain p)
    (h27 : ¬ lowerA p 27) (h34 : ¬ lowerA p 34)
    (h : lowerEarlyTerminalRequiredSound C p 2) (ha : lowerEarlyTerminalAt p (lowerEarlyTerminalHyp C 2)) :
    lowerEarlyTerminalListGeometry p (lowerEarlyTerminalTerminal (lowerEarlyTerminalPrimary p)) := by
  sorry

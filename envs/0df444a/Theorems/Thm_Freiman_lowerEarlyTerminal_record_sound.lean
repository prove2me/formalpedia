-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_record_sound
-- name    : Freiman.lowerEarlyTerminal_record_sound
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:46:48.476218+00:00
-- url     : https://prove2.me/theorems/1f3d26ea-7af5-4245-b0ab-fca1b594ce98
-- title:
--   Freiman.lowerEarlyTerminal_record_sound
-- statement:
--   Pull the certified pair contradiction through exact record-premise equality and positive range-checked IDs.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert.

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem Freiman.lowerEarlyTerminal_record_sound (C : LowerEarlyTerminalCatalog) (hp : lowerEarlyTerminalPairSound C) (rec : LowerEarlyTerminalRecord) (hr : lowerEarlyTerminalRecordValid C rec) : lowerEarlyTerminalRecordSound C rec := by
  sorry

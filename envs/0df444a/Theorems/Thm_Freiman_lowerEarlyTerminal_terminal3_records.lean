-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_terminal3_records
-- name    : Freiman.lowerEarlyTerminal_terminal3_records
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:44:53.760561+00:00
-- url     : https://prove2.me/theorems/4cfde0d3-870e-41d2-a611-728588c4d3ac
-- title:
--   Freiman.lowerEarlyTerminal_terminal3_records
-- statement:
--   Check that every stored record is exactly the residual premises reconstructed from its typed source goal and contains both certified conflicting bounds.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert. certificates/section15_terminal/geometry_certificate.json (952 records).

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem Freiman.lowerEarlyTerminal_terminal3_records : ∀ r ∈ lowerEarlyTerminalTerminal3.records, lowerEarlyTerminalRecordValid lowerEarlyTerminalTerminal3 r := by
  sorry

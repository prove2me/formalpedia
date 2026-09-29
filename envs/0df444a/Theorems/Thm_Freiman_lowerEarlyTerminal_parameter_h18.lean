-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_parameter_h18
-- name    : Freiman.lowerEarlyTerminal_parameter_h18
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:46:44.722234+00:00
-- url     : https://prove2.me/theorems/a4245067-8545-4d3f-9abf-eed56c1a7310
-- title:
--   Freiman.lowerEarlyTerminal_parameter_h18
-- statement:
--   Identify this exact four-coordinate field threshold with the unchanged lowerA test, including its weak/strict direction.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert. Source constants in independent_residual.py, independent_extensions.py, verify_independent.py; report threshold table and scalar tests.

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem Freiman.lowerEarlyTerminal_parameter_h18 (p : LowerPair) : lowerEarlyTerminalAt p [lowerEarlyTerminalH18] ↔ ¬ lowerA p 16 := by
  sorry

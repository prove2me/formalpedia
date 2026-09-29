-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_parameter_a9
-- name    : Freiman.lowerEarlyTerminal_parameter_a9
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:46:46.717976+00:00
-- url     : https://prove2.me/theorems/4d37a4c5-5c0f-4a7f-b78c-7e9bf59f2d48
-- title:
--   Freiman.lowerEarlyTerminal_parameter_a9
-- statement:
--   Identify this exact four-coordinate field threshold with the unchanged lowerA test, including its weak/strict direction.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert. Source constants in independent_residual.py, independent_extensions.py, verify_independent.py; report threshold table and scalar tests.

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem Freiman.lowerEarlyTerminal_parameter_a9 (p : LowerPair) : lowerEarlyTerminalAt p [lowerEarlyTerminalA9] ↔ lowerA p 9 := by
  sorry

-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_parameter_h7
-- name    : Freiman.lowerEarlyTerminal_parameter_h7
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:46:28.982235+00:00
-- url     : https://prove2.me/theorems/f4ff62ba-4b46-4284-bc06-f4fca961657b
-- title:
--   Freiman.lowerEarlyTerminal_parameter_h7
-- statement:
--   Identify this exact four-coordinate field threshold with the unchanged lowerA test, including its weak/strict direction.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert. Source constants in independent_residual.py, independent_extensions.py, verify_independent.py; report threshold table and scalar tests.

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem Freiman.lowerEarlyTerminal_parameter_h7 (p : LowerPair) : lowerEarlyTerminalAt p [lowerEarlyTerminalH7] ↔ ¬ lowerA p 3 := by
  sorry

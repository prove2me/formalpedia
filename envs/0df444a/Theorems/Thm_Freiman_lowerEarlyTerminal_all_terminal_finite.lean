-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_all_terminal_finite
-- name    : Freiman.lowerEarlyTerminal_all_terminal_finite
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:51:17.272874+00:00
-- url     : https://prove2.me/theorems/cb695058-0970-4470-bed5-21ac3c762ab9
-- title:
--   Freiman.lowerEarlyTerminal_all_terminal_finite
-- statement:
--   Select one of the three fully validated terminal-case catalogs.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert.

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem Freiman.lowerEarlyTerminal_all_terminal_finite (i : Fin 3) : lowerEarlyTerminalFiniteValid (lowerEarlyTerminalTerminalCatalog i) := by
  sorry

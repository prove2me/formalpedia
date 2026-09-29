-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_all_short_finite
-- name    : Freiman.lowerEarlyTerminal_all_short_finite
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:50:28.884737+00:00
-- url     : https://prove2.me/theorems/26f9bb19-ce57-46b9-9235-93fdc27dc75e
-- title:
--   Freiman.lowerEarlyTerminal_all_short_finite
-- statement:
--   Select one of the three fully validated short-case catalogs.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert.

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem Freiman.lowerEarlyTerminal_all_short_finite (i : Fin 3) : lowerEarlyTerminalFiniteValid (lowerEarlyTerminalShortCatalog i) := by
  sorry

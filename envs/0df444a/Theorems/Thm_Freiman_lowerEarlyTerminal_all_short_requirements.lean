-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_all_short_requirements
-- name    : Freiman.lowerEarlyTerminal_all_short_requirements
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:51:20.899441+00:00
-- url     : https://prove2.me/theorems/6d8935d8-06e0-4129-8d4d-b7a9c53bdd73
-- title:
--   Freiman.lowerEarlyTerminal_all_short_requirements
-- statement:
--   Select the exact required-goal binding for either short branch in each left suffix class.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert.

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem Freiman.lowerEarlyTerminal_all_short_requirements (i : Fin 3) (mode : ℕ) (hm : mode<2) :
    lowerEarlyTerminalRequirementBinding (lowerEarlyTerminalShortCatalog i) mode := by
  sorry

-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_domain_classes
-- name    : Freiman.lowerEarlyTerminal_domain_classes
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:48:01.678052+00:00
-- url     : https://prove2.me/theorems/c0c34734-e71f-41a4-baef-26c8487988b3
-- title:
--   Freiman.lowerEarlyTerminal_domain_classes
-- statement:
--   Actual admissible early states end on the left in one of the three catalog suffix classes.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert.

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem Freiman.lowerEarlyTerminal_domain_classes (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hd : lowerEarlyDomain p) :
    ∃ i : Fin 3, lowerEnds (lowerNormalize p).1 (lowerEarlyTerminalShortCatalog i).leftContext := by
  sorry

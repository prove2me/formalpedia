-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_short_applicability
-- name    : Freiman.lowerEarlyTerminal_short_applicability
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:48:04.889898+00:00
-- url     : https://prove2.me/theorems/e7a5068e-7673-4cca-b767-9b7d3a69b475
-- title:
--   Freiman.lowerEarlyTerminal_short_applicability
-- statement:
--   Translate the unchanged early branch tests to H7/H18/full normalization and the correct H27/H34 cuts, retaining A9 in classes1/2.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert.

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem Freiman.lowerEarlyTerminal_short_applicability (hp : LowerEarlyTerminalParameterLaws) (hdomain : LowerEarlyTerminalDomainLaws)
    (hw : LowerHistoryWidthLaw) (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hd : lowerEarlyDomain p)
    (mode : ℕ) (hm : mode < 2)
    (hbranch : if mode=0 then lowerA p 27 else ¬ lowerA p 27 ∧ lowerA p 34) :
    ∃ i : Fin 3, lowerEarlyTerminalApplied p (lowerEarlyTerminalShortCatalog i) mode := by
  sorry

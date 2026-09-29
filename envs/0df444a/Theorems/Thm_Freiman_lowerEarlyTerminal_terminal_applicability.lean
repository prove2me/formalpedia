-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_terminal_applicability
-- name    : Freiman.lowerEarlyTerminal_terminal_applicability
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:49:22.942734+00:00
-- url     : https://prove2.me/theorems/09769656-ba4e-4ee2-95ac-686af4dc9fe0
-- title:
--   Freiman.lowerEarlyTerminal_terminal_applicability
-- statement:
--   Translate actual terminal input to its exact catalog conditions. Complemented A27/A34 imply weak source upper bounds; A9 remains explicit for classes1/2.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert.

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem Freiman.lowerEarlyTerminal_terminal_applicability (hp : LowerEarlyTerminalParameterLaws) (hdomain : LowerEarlyTerminalDomainLaws)
    (hw : LowerHistoryWidthLaw) (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hd : lowerEarlyDomain p)
    (h27 : ¬ lowerA p 27) (h34 : ¬ lowerA p 34) (i : Fin 3)
    (he : lowerEnds (lowerNormalize p).1 (lowerEarlyTerminalTerminalCatalog i).leftContext) :
    lowerEarlyTerminalApplied p (lowerEarlyTerminalTerminalCatalog i) 2 := by
  sorry

-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_domain_context
-- name    : Freiman.lowerEarlyTerminal_domain_context
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:48:42.144478+00:00
-- url     : https://prove2.me/theorems/e4cbf9ac-03a2-4754-9a8f-d237c95bbf6c
-- title:
--   Freiman.lowerEarlyTerminal_domain_context
-- statement:
--   The actual normalized incoming words have the catalog suffix flags and equal common parity; ¬L prevents confusing a lone left1 context with suffix31.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert.

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem Freiman.lowerEarlyTerminal_domain_context (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hd : lowerEarlyDomain p)
    (C : LowerEarlyTerminalCatalog)
    (hc : C ∈ [lowerEarlyTerminalEarly3,lowerEarlyTerminalState1,lowerEarlyTerminalState2,lowerEarlyTerminalTerminal3])
    (he : lowerEnds (lowerNormalize p).1 C.leftContext) : lowerEarlyTerminalMatches p C := by
  sorry

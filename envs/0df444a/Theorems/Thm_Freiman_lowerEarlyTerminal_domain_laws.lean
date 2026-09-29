-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_domain_laws
-- name    : Freiman.lowerEarlyTerminal_domain_laws
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:48:48.12062+00:00
-- url     : https://prove2.me/theorems/ab5cafa7-e76b-4a5d-82ed-f4915f70633d
-- title:
--   Freiman.lowerEarlyTerminal_domain_laws
-- statement:
--   Package the three suffix classes, incoming orientation and exact source rectangles. This step contains only finite catalog selection.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert.

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem Freiman.lowerEarlyTerminal_domain_laws (hc : ∀ t p, lowerState t p → lowerEarlyDomain p →
      ∃ i : Fin 3, lowerEnds (lowerNormalize p).1 (lowerEarlyTerminalShortCatalog i).leftContext)
    (hf : ∀ t p, lowerState t p → lowerEarlyDomain p →
      ∀ C ∈ [lowerEarlyTerminalEarly3,lowerEarlyTerminalState1,lowerEarlyTerminalState2,lowerEarlyTerminalTerminal3],
        lowerEnds (lowerNormalize p).1 C.leftContext → lowerEarlyTerminalMatches p C)
    (hr : ∀ t p, lowerState t p → lowerEarlyDomain p →
      ∀ C ∈ [lowerEarlyTerminalEarly3,lowerEarlyTerminalState1,lowerEarlyTerminalState2,lowerEarlyTerminalTerminal3],
        lowerEnds (lowerNormalize p).1 C.leftContext →
          certRectangleMem C.rectangle (lowerEarlyTerminalR p) (lowerEarlyTerminalS p)) :
    LowerEarlyTerminalDomainLaws := by
  sorry

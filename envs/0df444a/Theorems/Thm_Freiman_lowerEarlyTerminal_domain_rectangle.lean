-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_domain_rectangle
-- name    : Freiman.lowerEarlyTerminal_domain_rectangle
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:49:29.690315+00:00
-- url     : https://prove2.me/theorems/97383988-1778-4295-becb-abd771f13e0b
-- title:
--   Freiman.lowerEarlyTerminal_domain_rectangle
-- statement:
--   Derive the three exact continuant-ratio rectangles from the actual source suffix states and admissible prefixes.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert. Class1: [1/2,4/5]×[3/4,4/5]; class2: [1/3,1/2]×[3/4,4/5]; class3: [1/4,1/3]×[3/4,4/5].

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem Freiman.lowerEarlyTerminal_domain_rectangle (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hd : lowerEarlyDomain p)
    (C : LowerEarlyTerminalCatalog)
    (hc : C ∈ [lowerEarlyTerminalEarly3,lowerEarlyTerminalState1,lowerEarlyTerminalState2,lowerEarlyTerminalTerminal3])
    (he : lowerEnds (lowerNormalize p).1 C.leftContext) : certRectangleMem C.rectangle (lowerEarlyTerminalR p) (lowerEarlyTerminalS p) := by
  sorry

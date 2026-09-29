-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_tie2_relaxation
-- name    : Freiman.lowerEarlyTerminal_tie2_relaxation
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:48:38.689977+00:00
-- url     : https://prove2.me/theorems/47ea17f4-648f-45bd-b1c4-ada9c42114b6
-- title:
--   Freiman.lowerEarlyTerminal_tie2_relaxation
-- statement:
--   At the exceptional virtual-right tie in the left2 class, the actual reflected fork covers contain the source fork covers. For digit1 only the local lower endpoint changes, and its change relaxes the contact; digit2 has no normalization tie.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert. Label22/32, source right digit1, virtual tie between U22 and V3211. Their ratios are near0.41 and0.59. The normalized shortening increment divided by full width increases with the denominator ratio, so moving the shortening to the lower-ratio side weakens the local lower endpoint. Odd common parity is the global sign dual. No equality under a tie is asserted.

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem Freiman.lowerEarlyTerminal_tie2_relaxation (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hd : lowerEarlyDomain p)
    (l : LowerLabel) (hn : lowerEarlyTerminalNative p l)
    (he : lowerEarlyTerminalTie2 p l) (hw : LowerHistoryWidthLaw) :
    ∃ norm : CertBound, (true,norm) ∈ section14NormalCases (section14LabelWords l) ∧
      lowerEarlyTerminalAt p [norm] ∧
      ∀ d ∈ ([1,2] : List ℕ+),
        lowerCover (lowerEarlyTerminalForkPair p l true d) ⊆
          lowerCover (lowerChild (lowerChild p l) ([d],[])) := by
  sorry

-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_child_goodness_regular
-- name    : Freiman.lowerEarlyTerminal_child_goodness_regular
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:48:24.357046+00:00
-- url     : https://prove2.me/theorems/0ddc7acf-2b97-4b8c-992c-2d5cb0b5d30e
-- title:
--   Freiman.lowerEarlyTerminal_child_goodness_regular
-- statement:
--   The actual native fork outside both exceptional equalities is good by finite ratio separation, strict normalization and the two certified source cross comparisons.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert.

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem Freiman.lowerEarlyTerminal_child_goodness_regular (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hd : lowerEarlyDomain p)
    (l : LowerLabel) (hn : lowerEarlyTerminalNative p l)
    (h2 : ¬ lowerEarlyTerminalTie2 p l) (h3 : ¬ lowerEarlyTerminalTie3 p l)
    (hw : LowerHistoryWidthLaw)
    (ho : ∀ w : LowerPair, lowerEndpoint w false ≤ lowerEndpoint w true) (h : ∀ req ∈ lowerEarlyTerminalGoodRequirements [] l, lowerEarlyTerminalAt p req.1 →
      lowerEarlyTerminalKindHolds p req.2) :
    lowerGood (lowerChild p l) := by
  sorry

-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_child_goodness
-- name    : Freiman.lowerEarlyTerminal_child_goodness
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:48:57.805304+00:00
-- url     : https://prove2.me/theorems/58839cd0-ddc8-49a6-be2b-19df061ef33d
-- title:
--   Freiman.lowerEarlyTerminal_child_goodness
-- statement:
--   Actual interior child goodness follows from the certified strict fork comparisons, with incoming-order normalization separated into regular, virtual-tie relaxation and impossible ordinary-tie cases.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert.

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem Freiman.lowerEarlyTerminal_child_goodness (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hd : lowerEarlyDomain p)
    (l : LowerLabel) (hn : lowerEarlyTerminalNative p l)
    (hw : LowerHistoryWidthLaw)
    (ho : ∀ w : LowerPair, lowerEndpoint w false ≤ lowerEndpoint w true) (h : ∀ req ∈ lowerEarlyTerminalGoodRequirements [] l, lowerEarlyTerminalAt p req.1 →
      lowerEarlyTerminalKindHolds p req.2) :
    lowerGood (lowerChild p l) := by
  sorry

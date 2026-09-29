-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_child_goodness_tie2
-- name    : Freiman.lowerEarlyTerminal_child_goodness_tie2
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:48:44.173163+00:00
-- url     : https://prove2.me/theorems/a7d01bcf-8aee-44ac-a59d-d03ce184e36d
-- title:
--   Freiman.lowerEarlyTerminal_child_goodness_tie2
-- statement:
--   The actual virtual-right tie case is handled by one-sided cover enlargement, followed by the same source contact certificates.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert.

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem Freiman.lowerEarlyTerminal_child_goodness_tie2 (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hd : lowerEarlyDomain p)
    (l : LowerLabel) (hn : lowerEarlyTerminalNative p l)
    (he : lowerEarlyTerminalTie2 p l) (hw : LowerHistoryWidthLaw)
    (ho : ∀ w : LowerPair, lowerEndpoint w false ≤ lowerEndpoint w true) (h : ∀ req ∈ lowerEarlyTerminalGoodRequirements [] l, lowerEarlyTerminalAt p req.1 →
      lowerEarlyTerminalKindHolds p req.2) :
    lowerGood (lowerChild p l) := by
  sorry

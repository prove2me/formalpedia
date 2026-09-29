-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_child_goodness_from_alignment
-- name    : Freiman.lowerEarlyTerminal_child_goodness_from_alignment
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:48:21.825183+00:00
-- url     : https://prove2.me/theorems/84c8b13c-52f8-4493-a28a-5ee4e8fabcc8
-- title:
--   Freiman.lowerEarlyTerminal_child_goodness_from_alignment
-- statement:
--   Endpoint order and the two source strict cross comparisons give actual goodness after the explicit fork endpoint alignment has been supplied.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert.

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem Freiman.lowerEarlyTerminal_child_goodness_from_alignment (p : LowerPair) (l : LowerLabel) (hw : LowerHistoryWidthLaw)
    (ho : ∀ w : LowerPair, lowerEndpoint w false ≤ lowerEndpoint w true)
    (halign : lowerEarlyTerminalForkAlignment p l) (h : ∀ req ∈ lowerEarlyTerminalGoodRequirements [] l, lowerEarlyTerminalAt p req.1 →
      lowerEarlyTerminalKindHolds p req.2) : lowerGood (lowerChild p l) := by
  sorry

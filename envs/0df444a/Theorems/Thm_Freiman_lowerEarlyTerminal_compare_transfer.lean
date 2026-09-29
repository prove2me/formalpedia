-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_compare_transfer
-- name    : Freiman.lowerEarlyTerminal_compare_transfer
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:46:04.973446+00:00
-- url     : https://prove2.me/theorems/0d332fdb-e24d-4d92-bceb-edd7c2723c7a
-- title:
--   Freiman.lowerEarlyTerminal_compare_transfer
-- statement:
--   Choose the actual two endpoint cases and turn their bound comparison into the requested real endpoint inequality.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert.

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem Freiman.lowerEarlyTerminal_compare_transfer (he : LowerEarlyTerminalEndpointLaw) (hg : LowerEarlyTerminalGreaterLaw)
    (C : LowerEarlyTerminalCatalog) (p : LowerPair) (hm : lowerEarlyTerminalMatches p C)
    (u v : LowerPair) (hi hj strict : Bool)
    (h : ∀ b ∈ lowerEarlyTerminalCompare C u hi v hj strict, lowerEarlyTerminalAt p b.1 →
      section14ComparisonHolds b.2 (lowerEarlyTerminalR p) (lowerEarlyTerminalS p) (lowerEarlyTerminalQ p)) :
    lowerEarlyTerminalKindHolds p (.compare u hi v hj strict) := by
  sorry

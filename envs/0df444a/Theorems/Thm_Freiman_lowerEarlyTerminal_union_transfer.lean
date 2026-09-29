-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_union_transfer
-- name    : Freiman.lowerEarlyTerminal_union_transfer
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:46:09.341824+00:00
-- url     : https://prove2.me/theorems/ea15102a-23fd-462e-ada7-cd9a7e05f1ab
-- title:
--   Freiman.lowerEarlyTerminal_union_transfer
-- statement:
--   All triple-endpoint cases imply the final disjunction. A single case is not assumed to imply the whole union join.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert. verify_independent.py: join-final-union; source endpoint disjunction rather than an adjacent-interval overclaim.

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem Freiman.lowerEarlyTerminal_union_transfer (he : LowerEarlyTerminalEndpointLaw) (hg : LowerEarlyTerminalGreaterLaw)
    (C : LowerEarlyTerminalCatalog) (p : LowerPair) (hm : lowerEarlyTerminalMatches p C)
    (h : ∀ b ∈ lowerEarlyTerminalUnionCases C, lowerEarlyTerminalAt p b.1 →
      section14ComparisonHolds b.2 (lowerEarlyTerminalR p) (lowerEarlyTerminalS p) (lowerEarlyTerminalQ p)) :
    lowerEarlyTerminalUnionHolds p := by
  sorry

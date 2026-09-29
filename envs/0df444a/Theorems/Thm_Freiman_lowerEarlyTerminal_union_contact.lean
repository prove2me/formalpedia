-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_union_contact
-- name    : Freiman.lowerEarlyTerminal_union_contact
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:50:23.758642+00:00
-- url     : https://prove2.me/theorems/c51207d7-c8dc-4310-895c-d141f217ef8b
-- title:
--   Freiman.lowerEarlyTerminal_union_contact
-- statement:
--   A two-interval connected terminal cluster intersects the preceding interval from the exact min-lower disjunction and reverse-anchor inequality.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert.

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem Freiman.lowerEarlyTerminal_union_contact (p : LowerPair) (a b c : LowerLabel)
    (ho : ∀ w : LowerPair, lowerEndpoint w false ≤ lowerEndpoint w true)
    (hbc : lowerEarlyTerminalContact p b c)
    (hforward : lowerEarlyTerminalEndpoint p (section14LabelWords b) false ≤ lowerEarlyTerminalEndpoint p (section14LabelWords a) true ∨
      lowerEarlyTerminalEndpoint p (section14LabelWords c) false ≤ lowerEarlyTerminalEndpoint p (section14LabelWords a) true)
    (hreverse : lowerEarlyTerminalEndpoint p (section14LabelWords a) false ≤ lowerEarlyTerminalEndpoint p (section14LabelWords c) true) :
    (lowerCover (lowerChild p a) ∩ (lowerCover (lowerChild p b) ∪ lowerCover (lowerChild p c))).Nonempty := by
  sorry

-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_cross_contact
-- name    : Freiman.lowerEarlyTerminal_cross_contact
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:48:18.890986+00:00
-- url     : https://prove2.me/theorems/08b4474f-5267-4710-bf36-a3d113d6c99a
-- title:
--   Freiman.lowerEarlyTerminal_cross_contact
-- statement:
--   Two cross endpoint comparisons plus individual endpoint order give actual interval intersection, with common-parity sign orientation accounted for.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert.

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem Freiman.lowerEarlyTerminal_cross_contact (p : LowerPair) (a b : LowerLabel)
    (ho : ∀ w : LowerPair, lowerEndpoint w false ≤ lowerEndpoint w true)
    (h1 : lowerEarlyTerminalKindHolds p (.compare (section14LabelWords a) true (section14LabelWords b) false false))
    (h2 : lowerEarlyTerminalKindHolds p (.compare (section14LabelWords b) true (section14LabelWords a) false false)) :
    lowerEarlyTerminalContact p a b := by
  sorry

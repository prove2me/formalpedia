-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_short_geometry
-- name    : Freiman.lowerEarlyTerminal_short_geometry
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:51:13.320923+00:00
-- url     : https://prove2.me/theorems/ecb92427-095f-4002-8d82-bc7a537f4046
-- title:
--   Freiman.lowerEarlyTerminal_short_geometry
-- statement:
--   Assemble the short-route source contacts, interior goodness, inherited trunk anchors and elementary interval gluing.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert.

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem Freiman.lowerEarlyTerminal_short_geometry (C : LowerEarlyTerminalCatalog) (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hd : lowerEarlyDomain p)
    (mode : ℕ) (hm : mode<2) (hb : if mode=0 then lowerA p 27 else ¬ lowerA p 27 ∧ lowerA p 34)
    (h : lowerEarlyTerminalRequiredSound C p mode)
    (ha : lowerEarlyTerminalAt p (lowerEarlyTerminalHyp C mode)) :
    lowerEarlyTerminalListGeometry p (if mode=0 then lowerEarlyTerminalFirst else lowerEarlyTerminalSecond) := by
  sorry

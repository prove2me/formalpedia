-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_short_ready
-- name    : Freiman.lowerEarlyTerminal_short_ready
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:50:42.670903+00:00
-- url     : https://prove2.me/theorems/75e3cfb5-3a59-40c9-8b68-8e3ad49f5aaa
-- title:
--   Freiman.lowerEarlyTerminal_short_ready
-- statement:
--   The complete catalog-to-source-to-interval reduction for each short branch, before identifying the unchanged lowerEarlyList.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert.

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem Freiman.lowerEarlyTerminal_short_ready (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hd : lowerEarlyDomain p)
    (mode : ℕ) (hm : mode<2)
    (hb : if mode=0 then lowerA p 27 else ¬ lowerA p 27 ∧ lowerA p 34) :
    lowerEarlyTerminalListGeometry p (if mode=0 then lowerEarlyTerminalFirst else lowerEarlyTerminalSecond) := by
  sorry

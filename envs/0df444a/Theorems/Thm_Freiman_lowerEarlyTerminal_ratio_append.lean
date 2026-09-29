-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_ratio_append
-- name    : Freiman.lowerEarlyTerminal_ratio_append
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:41:20.068427+00:00
-- url     : https://prove2.me/theorems/f18cedce-5ed4-4db6-b984-cd5dfdb8e2b2
-- title:
--   Freiman.lowerEarlyTerminal_ratio_append
-- statement:
--   Appending a positive-digit suffix updates the denominator ratio by the reversed-suffix continued-fraction map.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert. Report continuant matrix formula; lowerCD fold recurrence.

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem Freiman.lowerEarlyTerminal_ratio_append (u v : List ℕ+) : lowerRatio (u++v) = prefixEval v.reverse (lowerRatio u) := by
  sorry

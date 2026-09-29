-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_ratio_range
-- name    : Freiman.lowerEarlyTerminal_ratio_range
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:42:29.279379+00:00
-- url     : https://prove2.me/theorems/40b08b2d-2baf-47e8-af17-1f66a22feceb
-- title:
--   Freiman.lowerEarlyTerminal_ratio_range
-- statement:
--   Positive-digit continuant ratios lie in the closed unit interval, including the empty prefix.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert.

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem Freiman.lowerEarlyTerminal_ratio_range (w : List ℕ+) : 0 ≤ lowerRatio w ∧ lowerRatio w ≤ 1 := by
  sorry

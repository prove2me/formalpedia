-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_state1_requirements
-- name    : Freiman.lowerEarlyTerminal_state1_requirements
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:44:55.136083+00:00
-- url     : https://prove2.me/theorems/4cf72b82-e5c6-44a4-b4ae-329bc42635c5
-- title:
--   Freiman.lowerEarlyTerminal_state1_requirements
-- statement:
--   Check that all intervals, child-goodness comparisons, contacts and union alternatives required by each stated route occur among the certified source goals.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert. certificates/section15_early/extension_1.json (487 early plus920 terminal records).

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem Freiman.lowerEarlyTerminal_state1_requirements (mode : ℕ) (hm : mode ∈ [0, 1, 2]) : lowerEarlyTerminalRequirementBinding lowerEarlyTerminalState1 mode := by
  sorry

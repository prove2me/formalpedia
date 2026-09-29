-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_state2_goal_ids
-- name    : Freiman.lowerEarlyTerminal_state2_goal_ids
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:43:38.357173+00:00
-- url     : https://prove2.me/theorems/82634abc-f4a7-41db-9984-9437f0a9f80e
-- title:
--   Freiman.lowerEarlyTerminal_state2_goal_ids
-- statement:
--   Check all premise IDs and all scalar/union/endpoint branch ranges in this source family.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert. certificates/section15_early/extension_2.json (487 early plus920 terminal records).

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem Freiman.lowerEarlyTerminal_state2_goal_ids : ∀ g ∈ lowerEarlyTerminalState2.goals, lowerEarlyTerminalGoalValid lowerEarlyTerminalState2 g := by
  sorry

-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_fork_ranges
-- name    : Freiman.lowerEarlyTerminal_fork_ranges
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:42:32.531652+00:00
-- url     : https://prove2.me/theorems/a8813fb9-dc84-4235-b768-a444f01b12d7
-- title:
--   Freiman.lowerEarlyTerminal_fork_ranges
-- statement:
--   Check every ordinary and mixed virtual ratio interval of every actual interior label in the three source suffix classes. All intervals and their reflected intervals are disjoint except the two explicitly declared 22/32 cases.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert. The source lists in independent_residual.py, independent_extensions.py and verify_independent.py; exact finite table lowerEarlyTerminalForkCases generated from their native interior lists.

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem Freiman.lowerEarlyTerminal_fork_ranges : lowerEarlyTerminalForkRangesValid := by
  sorry

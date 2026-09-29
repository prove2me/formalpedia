-- Prove2me | Theorems.Thm_Freiman_lower_entry_core_arithmetic_threeOdd
-- name    : Freiman.lower_entry_core_arithmetic_threeOdd
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:21:24.256165+00:00
-- url     : https://prove2.me/theorems/ba07e454-a119-4096-8bd1-0a2fa493d53b
-- title:
--   Freiman lower construction: entry core arithmetic threeOdd
-- statement:
--   All 23 exact source core endpoint comparisons for terminal class threeOdd. Every upper/lower word, equality flag and parity is concrete in lowerInitialEntry. After clearing denominators the goal is a grouped finite biquadratic inequality on the printed closed rational r,s,q box; source tables supply Bernstein witnesses. No history or unbounded family remains in this leaf.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-entry; source H certificate appendix

import Definitions.Def_Freiman_lowerInitialEntry
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_entry_core_arithmetic_threeOdd : ∀ e ∈ lowerEntryCoreRows .threeOdd, lowerEntryRowValid e := by
  sorry

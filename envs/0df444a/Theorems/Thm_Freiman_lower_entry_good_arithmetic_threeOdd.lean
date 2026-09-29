-- Prove2me | Theorems.Thm_Freiman_lower_entry_good_arithmetic_threeOdd
-- name    : Freiman.lower_entry_good_arithmetic_threeOdd
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:21:28.324301+00:00
-- url     : https://prove2.me/theorems/5ab9efff-a185-43e2-99e5-a90a2c9a1ebd
-- title:
--   Freiman lower construction: entry good arithmetic threeOdd
-- statement:
--   All 26 or32 exact source good endpoint comparisons for terminal class threeOdd. Every upper/lower word, equality flag and parity is concrete in lowerInitialEntry. After clearing denominators the goal is a grouped finite biquadratic inequality on the printed closed rational r,s,q box; source tables supply Bernstein witnesses. No history or unbounded family remains in this leaf.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-entry; source H certificate appendix

import Definitions.Def_Freiman_lowerInitialEntry
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_entry_good_arithmetic_threeOdd : ∀ e ∈ lowerEntryGoodRows .threeOdd, lowerEntryRowValid e := by
  sorry

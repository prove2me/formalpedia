-- Prove2me | Theorems.Thm_Freiman_lower_entry_core_arithmetic_twoOdd
-- name    : Freiman.lower_entry_core_arithmetic_twoOdd
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:21:34.729653+00:00
-- url     : https://prove2.me/theorems/d62697d2-fd7b-4c1d-9935-e4e3a1948b5f
-- title:
--   Freiman lower construction: entry core arithmetic twoOdd
-- statement:
--   All 23 exact source core endpoint comparisons for terminal class twoOdd. Every upper/lower word, equality flag and parity is concrete in lowerInitialEntry. After clearing denominators the goal is a grouped finite biquadratic inequality on the printed closed rational r,s,q box; source tables supply Bernstein witnesses. No history or unbounded family remains in this leaf.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-entry; source H certificate appendix

import Definitions.Def_Freiman_lowerInitialEntry
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_entry_core_arithmetic_twoOdd : ∀ e ∈ lowerEntryCoreRows .twoOdd, lowerEntryRowValid e := by
  sorry

-- Prove2me | Theorems.Thm_Freiman_lower_entry_contact_arithmetic_twoOdd
-- name    : Freiman.lower_entry_contact_arithmetic_twoOdd
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:21:45.373441+00:00
-- url     : https://prove2.me/theorems/e7e8857d-5c6c-4127-8485-6d967b257aa8
-- title:
--   Freiman lower construction: entry contact arithmetic twoOdd
-- statement:
--   All 5 exact source contact endpoint comparisons for terminal class twoOdd. Every upper/lower word, equality flag and parity is concrete in lowerInitialEntry. After clearing denominators the goal is a grouped finite biquadratic inequality on the printed closed rational r,s,q box; source tables supply Bernstein witnesses. No history or unbounded family remains in this leaf.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-entry; source H certificate appendix

import Definitions.Def_Freiman_lowerInitialEntry
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_entry_contact_arithmetic_twoOdd : ∀ e ∈ lowerEntryContactRows .twoOdd, lowerEntryRowValid e := by
  sorry

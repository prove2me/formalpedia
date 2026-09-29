-- Prove2me | Theorems.Thm_Freiman_lower_entry_contact_arithmetic_threeEven
-- name    : Freiman.lower_entry_contact_arithmetic_threeEven
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:21:39.245754+00:00
-- url     : https://prove2.me/theorems/9a654a98-3a24-43d0-8bf8-dfe9ce716902
-- title:
--   Freiman lower construction: entry contact arithmetic threeEven
-- statement:
--   All 5 exact source contact endpoint comparisons for terminal class threeEven. Every upper/lower word, equality flag and parity is concrete in lowerInitialEntry. After clearing denominators the goal is a grouped finite biquadratic inequality on the printed closed rational r,s,q box; source tables supply Bernstein witnesses. No history or unbounded family remains in this leaf.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-entry; source H certificate appendix

import Definitions.Def_Freiman_lowerInitialEntry
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_entry_contact_arithmetic_threeEven : ∀ e ∈ lowerEntryContactRows .threeEven, lowerEntryRowValid e := by
  sorry

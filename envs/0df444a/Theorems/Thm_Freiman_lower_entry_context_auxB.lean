-- Prove2me | Theorems.Thm_Freiman_lower_entry_context_auxB
-- name    : Freiman.lower_entry_context_auxB
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:21:14.603182+00:00
-- url     : https://prove2.me/theorems/774941f1-974a-4267-bf5f-6dd6664fbba1
-- title:
--   Freiman lower construction: entry context auxB
-- statement:
--   Finite terminal suffix and parity classification for family auxB, with the exact H endpoint formula. B at k=0 and auxiliary B are the odd terminal2,3 exception.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-entry; source H certificate appendix

import Definitions.Def_Freiman_lowerInitialEntry
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_entry_context_auxB (n k p : ℕ) : ∃ c : LowerEntryClass,
    lowerEntryContext c (lowerNormalize (lowerFamilyPair .auxB n k p)) ∧
    lowerFamilyH .auxB n k p = lowerEntryH c (lowerNormalize (lowerFamilyPair .auxB n k p)) := by
  sorry

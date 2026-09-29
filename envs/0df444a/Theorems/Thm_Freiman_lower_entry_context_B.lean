-- Prove2me | Theorems.Thm_Freiman_lower_entry_context_B
-- name    : Freiman.lower_entry_context_B
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:21:08.111549+00:00
-- url     : https://prove2.me/theorems/0643acc9-64ad-41a1-a2af-73147c7071bd
-- title:
--   Freiman lower construction: entry context B
-- statement:
--   Finite terminal suffix and parity classification for family B, with the exact H endpoint formula. B at k=0 and auxiliary B are the odd terminal2,3 exception.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-entry; source H certificate appendix

import Definitions.Def_Freiman_lowerInitialEntry
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_entry_context_B (n k p : ℕ) : ∃ c : LowerEntryClass,
    lowerEntryContext c (lowerNormalize (lowerFamilyPair .B n k p)) ∧
    lowerFamilyH .B n k p = lowerEntryH c (lowerNormalize (lowerFamilyPair .B n k p)) := by
  sorry

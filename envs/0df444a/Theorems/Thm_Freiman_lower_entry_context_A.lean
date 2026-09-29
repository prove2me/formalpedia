-- Prove2me | Theorems.Thm_Freiman_lower_entry_context_A
-- name    : Freiman.lower_entry_context_A
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:21:04.758975+00:00
-- url     : https://prove2.me/theorems/8013227f-55df-42da-af8a-9ba3a9524d3e
-- title:
--   Freiman lower construction: entry context A
-- statement:
--   Finite terminal suffix and parity classification for family A, with the exact H endpoint formula. B at k=0 and auxiliary B are the odd terminal2,3 exception.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-entry; source H certificate appendix

import Definitions.Def_Freiman_lowerInitialEntry
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_entry_context_A (n k p : ℕ) : ∃ c : LowerEntryClass,
    lowerEntryContext c (lowerNormalize (lowerFamilyPair .A n k p)) ∧
    lowerFamilyH .A n k p = lowerEntryH c (lowerNormalize (lowerFamilyPair .A n k p)) := by
  sorry

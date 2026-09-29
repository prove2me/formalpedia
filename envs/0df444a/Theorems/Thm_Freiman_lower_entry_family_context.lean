-- Prove2me | Theorems.Thm_Freiman_lower_entry_family_context
-- name    : Freiman.lower_entry_family_context
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:21:36.238184+00:00
-- url     : https://prove2.me/theorems/136f3cd7-cef4-47ab-99cf-90dc041acaca
-- title:
--   Freiman lower construction: entry family context
-- statement:
--   (f : LowerInitialFamily) (n k p : ℕ) : ∃ c : LowerEntryClass,
--       lowerEntryContext c (lowerNormalize (lowerFamilyPair f n k p)) ∧
--       lowerFamilyH f n k p = lowerEntryH c (lowerNormalize (lowerFamilyPair f n k p))
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-entry; source H certificate appendix

import Definitions.Def_Freiman_lowerInitialEntry
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_entry_family_context (f : LowerInitialFamily) (n k p : ℕ) : ∃ c : LowerEntryClass,
    lowerEntryContext c (lowerNormalize (lowerFamilyPair f n k p)) ∧
    lowerFamilyH f n k p = lowerEntryH c (lowerNormalize (lowerFamilyPair f n k p)) := by
  sorry

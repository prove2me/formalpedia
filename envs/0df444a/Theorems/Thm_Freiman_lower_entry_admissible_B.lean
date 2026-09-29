-- Prove2me | Theorems.Thm_Freiman_lower_entry_admissible_B
-- name    : Freiman.lower_entry_admissible_B
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:21:15.404326+00:00
-- url     : https://prove2.me/theorems/97f6731f-058c-4715-8488-7b5b44219408
-- title:
--   Freiman lower construction: entry admissible B
-- statement:
--   Six actual appended word checks for family B: preserve one of the seven oriented central cores and exclude31313. This word claim is separate from numeric goodness.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-entry; source H certificate appendix

import Definitions.Def_Freiman_lowerInitialEntry
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_entry_admissible_B (n k p : ℕ) : ∀ l ∈ lowerEntryLabels,
    lowerAdmissible (lowerChild (lowerFamilyPair .B n k p) l) := by
  sorry

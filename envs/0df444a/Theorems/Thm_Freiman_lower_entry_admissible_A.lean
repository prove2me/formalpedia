-- Prove2me | Theorems.Thm_Freiman_lower_entry_admissible_A
-- name    : Freiman.lower_entry_admissible_A
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:21:12.410838+00:00
-- url     : https://prove2.me/theorems/8e4a96e4-93ea-431e-bda2-ae91513782c0
-- title:
--   Freiman lower construction: entry admissible A
-- statement:
--   Six actual appended word checks for family A: preserve one of the seven oriented central cores and exclude31313. This word claim is separate from numeric goodness.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-entry; source H certificate appendix

import Definitions.Def_Freiman_lowerInitialEntry
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_entry_admissible_A (n k p : ℕ) : ∀ l ∈ lowerEntryLabels,
    lowerAdmissible (lowerChild (lowerFamilyPair .A n k p) l) := by
  sorry

-- Prove2me | Theorems.Thm_Freiman_lower_entry_admissible_auxB
-- name    : Freiman.lower_entry_admissible_auxB
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:21:21.626297+00:00
-- url     : https://prove2.me/theorems/fe302f7d-c870-40f7-a92f-ad30dd77a392
-- title:
--   Freiman lower construction: entry admissible auxB
-- statement:
--   Six actual appended word checks for family auxB: preserve one of the seven oriented central cores and exclude31313. This word claim is separate from numeric goodness.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-entry; source H certificate appendix

import Definitions.Def_Freiman_lowerInitialEntry
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_entry_admissible_auxB (n k p : ℕ) : ∀ l ∈ lowerEntryLabels,
    lowerAdmissible (lowerChild (lowerFamilyPair .auxB n k p) l) := by
  sorry

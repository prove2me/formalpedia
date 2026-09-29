-- Prove2me | Theorems.Thm_Freiman_lower_entry_admissible_C
-- name    : Freiman.lower_entry_admissible_C
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:21:18.765703+00:00
-- url     : https://prove2.me/theorems/fc131292-f148-4e5a-817e-76f0153b55de
-- title:
--   Freiman lower construction: entry admissible C
-- statement:
--   Six actual appended word checks for family C: preserve one of the seven oriented central cores and exclude31313. This word claim is separate from numeric goodness.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-entry; source H certificate appendix

import Definitions.Def_Freiman_lowerInitialEntry
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_entry_admissible_C (n k p : ℕ) : ∀ l ∈ lowerEntryLabels,
    lowerAdmissible (lowerChild (lowerFamilyPair .C n k p) l) := by
  sorry

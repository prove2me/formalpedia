-- Prove2me | Theorems.Thm_Freiman_lower_entry_admissible
-- name    : Freiman.lower_entry_admissible
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:21:17.83061+00:00
-- url     : https://prove2.me/theorems/e297c63d-75df-4c75-93fa-d54bad636d05
-- title:
--   Freiman lower construction: entry admissible
-- statement:
--   (f : LowerInitialFamily) (n k p : ℕ) : ∀ l ∈ lowerEntryLabels, lowerAdmissible (lowerChild (lowerFamilyPair f n k p) l)
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-entry; source H certificate appendix

import Definitions.Def_Freiman_lowerInitialEntry
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_entry_admissible (f : LowerInitialFamily) (n k p : ℕ) : ∀ l ∈ lowerEntryLabels, lowerAdmissible (lowerChild (lowerFamilyPair f n k p) l) := by
  sorry

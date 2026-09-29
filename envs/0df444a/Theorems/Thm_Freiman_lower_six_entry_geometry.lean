-- Prove2me | Theorems.Thm_Freiman_lower_six_entry_geometry
-- name    : Freiman.lower_six_entry_geometry
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:15:17.89899+00:00
-- url     : https://prove2.me/theorems/e3a42852-2716-4fbf-bde3-6e1bfb6a4c7f
-- title:
--   Freiman lower construction: six entry geometry
-- statement:
--   The six actual child intervals are admissible, good and within the uniform parameter box; their union covers H, with actual endpoint shortening and renormalization.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-entry

import Definitions.Def_Freiman_lowerInitialEntry
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_six_entry_geometry : ∀ (f : LowerInitialFamily) (n k p : ℕ),
    (∀ l ∈ lowerEntryLabels, lowerAdmissible (lowerChild (lowerFamilyPair f n k p) l) ∧
      lowerGood (lowerChild (lowerFamilyPair f n k p) l) ∧ lowerParameterBox (lowerChild (lowerFamilyPair f n k p) l)) ∧
    lowerFamilyH f n k p ⊆ {t | ∃ l ∈ lowerEntryLabels, t ∈ lowerCover (lowerChild (lowerFamilyPair f n k p) l)} := by
  sorry

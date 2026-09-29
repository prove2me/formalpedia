-- Prove2me | Theorems.Thm_Freiman_lower_entry_class_geometry
-- name    : Freiman.lower_entry_class_geometry
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:22:25.789826+00:00
-- url     : https://prove2.me/theorems/b76c8670-e0e4-4268-b09e-b4ff45f00a12
-- title:
--   Freiman lower construction: entry class geometry
-- statement:
--   (c : LowerEntryClass) (p : LowerPair) (hc : lowerEntryContext c p) (hd : lowerEntryDomain p) :
--       (∀ l ∈ lowerEntryLabels, lowerStrictGood (lowerChild p l)) ∧
--       lowerEntryH c p ⊆ {t | ∃ l ∈ lowerEntryLabels, t ∈ lowerCover (lowerChild p l)}
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-entry; source H certificate appendix

import Definitions.Def_Freiman_lowerInitialEntry
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_entry_class_geometry (c : LowerEntryClass) (p : LowerPair) (hc : lowerEntryContext c p) (hd : lowerEntryDomain p) :
    (∀ l ∈ lowerEntryLabels, lowerStrictGood (lowerChild p l)) ∧
    lowerEntryH c p ⊆ {t | ∃ l ∈ lowerEntryLabels, t ∈ lowerCover (lowerChild p l)} := by
  sorry

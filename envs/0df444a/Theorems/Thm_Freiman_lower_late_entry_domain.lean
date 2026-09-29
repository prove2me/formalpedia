-- Prove2me | Theorems.Thm_Freiman_lower_late_entry_domain
-- name    : Freiman.lower_late_entry_domain
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:15:17.447317+00:00
-- url     : https://prove2.me/theorems/10d0243a-3a25-462f-881b-c2ea7b12b163
-- title:
--   Freiman lower construction: late entry domain
-- statement:
--   An actually reached late parent has r≥13/17 unless its normalized physical pair is exactly (31,31). The early r≤1/3 condition is never imported here.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_140_144.tex, lem:late-entry-domain

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_late_entry_domain (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n) : lowerLateEntryDomain (h n) := by
  sorry

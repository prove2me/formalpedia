-- Prove2me | Theorems.Thm_Freiman_lower_family_root
-- name    : Freiman.lower_family_root
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:15:05.358709+00:00
-- url     : https://prove2.me/theorems/58accaa2-6df1-41ea-937c-25f2433c945c
-- title:
--   Freiman lower construction: family root
-- statement:
--   (t : ℝ) (ht : ∃ (f : LowerInitialFamily) (n k p : ℕ), t ∈ lowerFamilyH f n k p) :
--       ∃ r : LowerPair, lowerInitialRoot t r ∧ lowerState t r
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/initial_bridges.tex, initial selection

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_family_root (t : ℝ) (ht : ∃ (f : LowerInitialFamily) (n k p : ℕ), t ∈ lowerFamilyH f n k p) :
    ∃ r : LowerPair, lowerInitialRoot t r ∧ lowerState t r := by
  sorry

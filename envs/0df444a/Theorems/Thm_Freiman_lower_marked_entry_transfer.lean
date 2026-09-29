-- Prove2me | Theorems.Thm_Freiman_lower_marked_entry_transfer
-- name    : Freiman.lower_marked_entry_transfer
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:15:08.576986+00:00
-- url     : https://prove2.me/theorems/b1fd062c-59ed-474e-ab94-697e186ab7f1
-- title:
--   Freiman lower construction: marked entry transfer
-- statement:
--   Finite A0/An/B bridge transfer plus the C-to-B overlap, retaining B-first priority and the exact marked-entry target bound. It uses the six ordinary entry covers supplied in the hypothesis.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/initial_bridges.tex, lem:H-entry-bridges and initial selection

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_marked_entry_transfer (hentry : ∀ (f : LowerInitialFamily) (n k p : ℕ), (∀ l ∈ lowerEntryLabels, lowerAdmissible (lowerChild (lowerFamilyPair f n k p) l) ∧ lowerGood (lowerChild (lowerFamilyPair f n k p) l) ∧ lowerParameterBox (lowerChild (lowerFamilyPair f n k p) l)) ∧ lowerFamilyH f n k p ⊆ {t | ∃ l ∈ lowerEntryLabels, t ∈ lowerCover (lowerChild (lowerFamilyPair f n k p) l)})
    (t : ℝ) (f : LowerInitialFamily) (n k p : ℕ) (ht : lowerInitialBaseSelected t f n k p) :
    ∃ r : LowerPair, lowerInitialRoot t r ∧ lowerState t r := by
  sorry

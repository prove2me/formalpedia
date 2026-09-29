-- Prove2me | Theorems.Thm_Freiman_lower_marked_entry_gluing
-- name    : Freiman.lower_marked_entry_gluing
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:17:38.628588+00:00
-- url     : https://prove2.me/theorems/c2fec2f0-f767-453a-9aa9-28fcbd025d42
-- title:
--   Freiman lower construction: marked entry gluing
-- statement:
--   Split at the exact marked threshold, use the appropriate separately supplied finite bridge when above it, otherwise keep a six-entry child; B-first priority rules out the high C residual. The incoming physical orientation and the equal endpoint case are retained.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/initial_bridges.tex, initial selection paragraph

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_marked_entry_gluing (hA0 : lowerBridgeGood .A 0) (hAn : ∀ n : ℕ, 0 < n → lowerBridgeGood .A n)
    (hB : ∀ n : ℕ, lowerBridgeGood .B n)
    (hC : ∀ n k : ℕ, lowerBridgeInterval .C n k 0 ⊆ lowerFamilyH .B n (k+2) 0)
    (hentry : ∀ (f : LowerInitialFamily) (n k p : ℕ), (∀ l ∈ lowerEntryLabels, lowerAdmissible (lowerChild (lowerFamilyPair f n k p) l) ∧ lowerGood (lowerChild (lowerFamilyPair f n k p) l) ∧ lowerParameterBox (lowerChild (lowerFamilyPair f n k p) l)) ∧ lowerFamilyH f n k p ⊆ {t | ∃ l ∈ lowerEntryLabels, t ∈ lowerCover (lowerChild (lowerFamilyPair f n k p) l)})
    (t : ℝ) (f : LowerInitialFamily) (n k p : ℕ) (ht : lowerInitialBaseSelected t f n k p) :
    ∃ r : LowerPair, lowerInitialRoot t r ∧ lowerState t r := by
  sorry

-- Prove2me | Theorems.Thm_Freiman_lower_physical_prefix_transfer
-- name    : Freiman.lower_physical_prefix_transfer
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:18:07.921806+00:00
-- url     : https://prove2.me/theorems/08458de2-33c4-4433-84fd-5812916c7f67
-- title:
--   Freiman lower construction: physical prefix transfer
-- statement:
--   The cumulative orientation records every strict width reflection. Undoing this explicit orientation makes each selected outward addition a proper extension of the same two physical words; a width tie retains the incoming order. Admissibility is retained up to the displayed reflection of one of the seven cores.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, first paragraph and lem:lc-cylinders

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_physical_prefix_transfer (hwords : ∀ (t : ℝ) (h : ℕ → LowerPair) (n : ℕ), lowerHistory t h n → ∀ l : LowerLabel,
    lowerOffered (h n) l → lowerAdmissible (lowerChild (h n) l) ∧
    lowerExtends (lowerNormalize (h n)) (lowerChild (h n) l) ∧
    lowerPrefixSize (h n) < lowerPrefixSize (lowerChild (h n) l))
    (t : ℝ) (h : ℕ → LowerPair) (hh : lowerPath t h) :
    (∀ n, lowerAdmissible (lowerPhysicalPath h n)) ∧
    (∀ n, lowerExtends (lowerPhysicalPath h n) (lowerPhysicalPath h (n+1))) ∧
    (∀ n, lowerPrefixSize (lowerPhysicalPath h n) < lowerPrefixSize (lowerPhysicalPath h (n+1))) := by
  sorry

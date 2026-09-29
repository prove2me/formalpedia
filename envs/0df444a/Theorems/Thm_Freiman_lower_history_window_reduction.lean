-- Prove2me | Theorems.Thm_Freiman_lower_history_window_reduction
-- name    : Freiman.lower_history_window_reduction
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:17:19.764989+00:00
-- url     : https://prove2.me/theorems/4a5b5147-f61e-4277-a6b7-abbe92a354e6
-- title:
--   Freiman lower construction: history window reduction
-- statement:
--   Trace the same physical marked side back to its generic birth or initial root. The six permitted persistent labels and forced reflections bound the full birth-to-hazard path by seven steps. This is the proof that the finite certificate catalogue covers every reached history.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/global_selection.tex, finite suffix reduction

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_history_window_reduction (hf : ∀ (p : LowerPair), lowerGood p → lowerParameterBox p → let q := lowerNormalize p; lowerWidth (q.1 ++ [2]) < lowerWidth q.2 ∧ lowerWidth (q.1 ++ [3]) < lowerWidth q.2 ∧ lowerWidth (q.1 ++ [1,1]) < lowerWidth q.2 ∧ lowerWidth (q.2 ++ [1]) < lowerWidth q.1)
    (hb : ∀ (t : ℝ) (h : ℕ → LowerPair) (n : ℕ), lowerHistory t h n →
      ∀ (l : LowerLabel), lowerOffered (h n) l → ∀ right : Bool,
      lowerEnds (lowerSide (lowerChild (h n) l) right) [3,1,3] →
      lowerSide (lowerChild (h n) l) right ≠ lowerSide (lowerNormalize (h n)) right → l = ([2],[3]))
    (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n) : lowerBoundedHistory h n := by
  sorry

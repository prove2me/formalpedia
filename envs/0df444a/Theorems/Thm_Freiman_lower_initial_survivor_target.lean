-- Prove2me | Theorems.Thm_Freiman_lower_initial_survivor_target
-- name    : Freiman.lower_initial_survivor_target
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:18:08.200393+00:00
-- url     : https://prove2.me/theorems/6a917606-4801-4cc4-99c0-70f6872dcb55
-- title:
--   Freiman lower construction: initial survivor target
-- statement:
--   The two surviving initial catalog paths end at S=(U1,V1). Its C22 child is exactly (U12,V12), and changing to the even local coordinates reverses the carried safe threshold. This uses the corrected bridge rule, not the eight discarded attempted bounds in initial_histories.json.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/initial_bridges.tex, corrected surviving S contexts; global_selection.tex, marked initial row2

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_initial_survivor_target (t : ℝ) (f : LowerInitialFamily) (n k p : ℕ)
    (hmarked : (f = .A ∧ k = 0) ∨ (f = .B ∧ k = 0) ∨ (f = .C ∧ p = 0))
    (hsafe : lowerInitialSafeBound t f n k p) (s : LowerPair)
    (hnorm : lowerNormalize s =
      ((lowerNormalize (lowerFamilyPair f n k p)).1 ++ [1],
       (lowerNormalize (lowerFamilyPair f n k p)).2 ++ [1])) :
    lowerLocalLower s ([2],[2]) ≤ lowerLocalCoordinate s t := by
  sorry

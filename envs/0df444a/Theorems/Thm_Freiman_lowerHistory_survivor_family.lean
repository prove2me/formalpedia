-- Prove2me | Theorems.Thm_Freiman_lowerHistory_survivor_family
-- name    : Freiman.lowerHistory_survivor_family
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:32:08.569816+00:00
-- url     : https://prove2.me/theorems/52ce4951-f4e6-42c6-b89e-0d2c5c20823f
-- title:
--   Freiman.lowerHistory_survivor_family
-- statement:
--   H182/H374 have exactly the reflected 10 then10 path S=(U1,V1); recover the selected-family safe-bound hypothesis for the corrected J12,12 bridge.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026); initial_bridges.tex, lem:H-entry-bridges; global_selection.tex, lem:global-suffix-targets; history_certificates.tex, app:all-suffix-histories; verification/families/target_selection/verify_H_entry_reduction_independent.py; certificates/target_selection/initial_histories.json; role: corrected H-entry two survivors

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic

open Freiman

theorem Freiman.lowerHistory_survivor_family (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n)
    (base : LowerPair) (p : LowerHistoryPath) (hp : lowerHistoryStructural p) (hr : lowerHistoryReached t h n base p) (hs : lowerHistorySurvivor p) :
    ∃ (f : LowerInitialFamily) (a k v : ℕ),
      ((f = .A ∧ k = 0) ∨ (f = .B ∧ k = 0) ∨ (f = .C ∧ v = 0)) ∧
      lowerInitialSafeBound t f a k v ∧ lowerNormalize (h n) =
        ((lowerNormalize (lowerFamilyPair f a k v)).1++[1],
         (lowerNormalize (lowerFamilyPair f a k v)).2++[1]) := by
  sorry

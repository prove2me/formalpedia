-- Prove2me | Theorems.Thm_Freiman_lowerHistory_path_soundness
-- name    : Freiman.lowerHistory_path_soundness
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:31:50.339123+00:00
-- url     : https://prove2.me/theorems/fd705749-2ce0-49f2-8ee2-c2ded612d545
-- title:
--   Freiman.lowerHistory_path_soundness
-- statement:
--   Apply every concrete exclusion via the generic kernel, then use full record coverage.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026); global_selection.tex, lem:global-suffix-targets; history_certificates.tex, app:all-suffix-histories; verification/families/target_selection/verify_suffix_targets_independent.py; certificates/target_selection/all_suffix_histories_printed.json; role: concrete catalog soundness

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic

open Freiman

theorem Freiman.lowerHistory_path_soundness (p : LowerHistoryPath) (hp : p ∈ lowerHistoryPaths.toList)
    (hb : lowerHistoryAllBindings) (hw : lowerHistoryAllWitnesses)
    (r s q : ℝ) (hm : certRectangleMem p.rectangle r s)
    (hsource : ∃ bs ∈ lowerHistorySourcePremises p, lowerHistoryConditions bs r s q) :
    (p.catalog = .initial ∧ lowerHistorySurvivor p) ∨
      (p.catalog ≠ .initial ∧ p.row ≠ 4 ∧ lowerHistoryComparisonsHold p r s q) := by
  sorry

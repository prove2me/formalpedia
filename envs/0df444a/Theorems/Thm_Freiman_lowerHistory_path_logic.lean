-- Prove2me | Theorems.Thm_Freiman_lowerHistory_path_logic
-- name    : Freiman.lowerHistory_path_logic
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:31:48.007902+00:00
-- url     : https://prove2.me/theorems/5c6e117c-ce23-4970-a318-4f94eeb0cec5
-- title:
--   Freiman.lowerHistory_path_logic
-- statement:
--   Finite alternative and endpoint-mode coverage leaves only the two named initial survivors, or proves every needed generic endpoint comparison.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026); global_selection.tex, lem:global-suffix-targets; history_certificates.tex, app:all-suffix-histories; verification/families/target_selection/verify_suffix_targets_independent.py; certificates/target_selection/all_suffix_histories_printed.json; role: finite certificate completeness

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic

open Freiman

theorem Freiman.lowerHistory_path_logic (hneg : ∀ (b : CertBound) (r s q : ℝ), certBoundHolds (lowerHistoryComplement b) r s q ↔ ¬ certBoundHolds b r s q) (p : LowerHistoryPath) (hb : lowerHistoryPathBinding p)
    (r s q : ℝ) (hsource : ∃ bs ∈ lowerHistorySourcePremises p, lowerHistoryConditions bs r s q)
    (hex : ∀ record ∈ lowerHistoryRecordsFor p, record.survivor = false →
      ¬ lowerHistoryConditions (lowerHistoryResidual p record.alternative record.endpointBranch) r s q) :
    (p.catalog = .initial ∧ lowerHistorySurvivor p) ∨
      (p.catalog ≠ .initial ∧ p.row ≠ 4 ∧ lowerHistoryComparisonsHold p r s q) := by
  sorry

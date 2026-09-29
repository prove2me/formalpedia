-- Prove2me | Theorems.Thm_Freiman_lowerHistory_complement
-- name    : Freiman.lowerHistory_complement
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:24:20.749986+00:00
-- url     : https://prove2.me/theorems/a633c192-02cc-453f-af8f-d720734d28e0
-- title:
--   Freiman.lowerHistory_complement
-- statement:
--   Negating a q-bound reverses its side and toggles strictness.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026); global_selection.tex, lem:global-suffix-targets; history_certificates.tex, app:all-suffix-histories; verification/families/target_selection/verify_suffix_targets_independent.py; certificates/target_selection/all_suffix_histories_printed.json; role: certificate semantics

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic

open Freiman

theorem Freiman.lowerHistory_complement (b : CertBound) (r s q : ℝ) :
    certBoundHolds (lowerHistoryComplement b) r s q ↔ ¬ certBoundHolds b r s q := by
  sorry

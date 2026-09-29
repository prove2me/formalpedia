-- Prove2me | Theorems.Thm_Freiman_lowerHistory_sign_value
-- name    : Freiman.lowerHistory_sign_value
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:23:27.652207+00:00
-- url     : https://prove2.me/theorems/ffe7e5ae-08e8-44da-8ad1-e1e9626ccc44
-- title:
--   Freiman.lowerHistory_sign_value
-- statement:
--   Exact sign in Q(sqrt3,sqrt7), assembled from the quadratic sign lemma.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026); lower_core.tex, eq:lc-difference and eq:lc-full-width; history_certificates.tex, app:all-suffix-histories; verification/families/section15_late/independent_engine.py and verification/families/target_selection/verify_h5_original_independent.py; role: certificate field arithmetic

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic

open Freiman

theorem Freiman.lowerHistory_sign_value (z : CertField) :
    (lowerHistorySign z = 0 ↔ certFieldVal z = 0) ∧ (0 < lowerHistorySign z ↔ 0 < certFieldVal z) := by
  sorry

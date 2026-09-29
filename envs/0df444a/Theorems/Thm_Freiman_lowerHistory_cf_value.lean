-- Prove2me | Theorems.Thm_Freiman_lowerHistory_cf_value
-- name    : Freiman.lowerHistory_cf_value
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:23:30.334669+00:00
-- url     : https://prove2.me/theorems/cc7649bb-aa25-4176-9671-b7770cd4a477
-- title:
--   Freiman.lowerHistory_cf_value
-- statement:
--   Source exact CF evaluation is connected to the mission prefixEval definition.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026); lower_core.tex, eq:lc-difference and eq:lc-full-width; history_certificates.tex, app:all-suffix-histories; verification/families/section15_late/independent_engine.py and verification/families/target_selection/verify_h5_original_independent.py; role: source Möbius formula

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic

open Freiman

theorem Freiman.lowerHistory_cf_value (w : List ℕ+) (z : CertField) (hz : 0 ≤ certFieldVal z) :
    certFieldVal (lowerHistoryCF w z) = prefixEval w (certFieldVal z) := by
  sorry

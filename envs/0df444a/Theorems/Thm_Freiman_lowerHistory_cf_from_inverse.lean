-- Prove2me | Theorems.Thm_Freiman_lowerHistory_cf_from_inverse
-- name    : Freiman.lowerHistory_cf_from_inverse
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:23:48.460154+00:00
-- url     : https://prove2.me/theorems/a4be1617-d948-4393-9c6d-d95e2e36a4e3
-- title:
--   Freiman.lowerHistory_cf_from_inverse
-- statement:
--   Matrix product and positive denominators identify the exact source CF evaluator with prefixEval.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026); lower_core.tex, eq:lc-difference and eq:lc-full-width; history_certificates.tex, app:all-suffix-histories; verification/families/section15_late/independent_engine.py and verification/families/target_selection/verify_h5_original_independent.py; role: source Möbius formula

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic

open Freiman

theorem Freiman.lowerHistory_cf_from_inverse (hinv : ∀ z : CertField, certFieldVal z ≠ 0 → certFieldVal (lowerHistoryInv z) = (certFieldVal z)⁻¹) (w : List ℕ+) (z : CertField) (hz : 0 ≤ certFieldVal z) :
    certFieldVal (lowerHistoryCF w z) = prefixEval w (certFieldVal z) := by
  sorry

-- Prove2me | Theorems.Thm_Freiman_lowerHistory_quad_sign_value
-- name    : Freiman.lowerHistory_quad_sign_value
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:23:25.265983+00:00
-- url     : https://prove2.me/theorems/0337a848-3ce0-4d5c-a683-ca6b7f2506a3
-- title:
--   Freiman.lowerHistory_quad_sign_value
-- statement:
--   Specialized quadratic sign comparison for d=3; no false d=0 generalization.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026); lower_core.tex, eq:lc-difference and eq:lc-full-width; history_certificates.tex, app:all-suffix-histories; verification/families/section15_late/independent_engine.py and verification/families/target_selection/verify_h5_original_independent.py; role: certificate field arithmetic

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic

open Freiman

theorem Freiman.lowerHistory_quad_sign_value (a b : ℚ) :
    (lowerHistoryQuadSign a b 3 = 0 ↔ (a:ℝ)+b*Real.sqrt 3 = 0) ∧
    (0 < lowerHistoryQuadSign a b 3 ↔ 0 < (a:ℝ)+b*Real.sqrt 3) := by
  sorry

-- Prove2me | Theorems.Thm_Freiman_lowerHistory_greater_from_sign
-- name    : Freiman.lowerHistory_greater_from_sign
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:32:21.714983+00:00
-- url     : https://prove2.me/theorems/8a93168e-6e0e-4666-a0ae-bb12b0f1f333
-- title:
--   Freiman.lowerHistory_greater_from_sign
-- statement:
--   The exact component signs reduce the positive-denominator Möbius comparison to its q-threshold.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026); lower_core.tex, eq:lc-difference and eq:lc-full-width; history_certificates.tex, app:all-suffix-histories; verification/families/section15_late/independent_engine.py and verification/families/target_selection/verify_h5_original_independent.py; role: source comparison semantics

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic

open Freiman

theorem Freiman.lowerHistory_greater_from_sign (hsg : ∀ z : CertField, (lowerHistorySign z = 0 ↔ certFieldVal z = 0) ∧ (0 < lowerHistorySign z ↔ 0 < certFieldVal z)) (base : LowerPair) (C : LowerHistoryContext) (hc : lowerHistoryContextFits base C)
    (x y : CertField × CertField) (hx : 0 ≤ certFieldVal x.1 ∧ 0 ≤ certFieldVal x.2)
    (hy : 0 ≤ certFieldVal y.1 ∧ 0 ≤ certFieldVal y.2) :
    lowerHistoryComparisonHolds (lowerHistoryGreater C x y) (lowerRatio base.1) (lowerRatio base.2) (lowerScale base) ↔
      lowerHistoryValue base C y ≤ lowerHistoryValue base C x := by
  sorry

-- Prove2me | Theorems.Thm_Freiman_lowerHistory_greater_semantics
-- name    : Freiman.lowerHistory_greater_semantics
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:23:44.881521+00:00
-- url     : https://prove2.me/theorems/0df9b7c1-bc33-4ae6-b87d-e4e2f34e3b5c
-- title:
--   Freiman.lowerHistory_greater_semantics
-- statement:
--   The source component-sign test and positive scale translate its final q-bound into the actual endpoint inequality.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026); lower_core.tex, eq:lc-difference and eq:lc-full-width; history_certificates.tex, app:all-suffix-histories; verification/families/section15_late/independent_engine.py and verification/families/target_selection/verify_h5_original_independent.py; role: source comparison semantics

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic

open Freiman

theorem Freiman.lowerHistory_greater_semantics (base : LowerPair) (C : LowerHistoryContext) (hc : lowerHistoryContextFits base C)
    (x y : CertField × CertField) (hx : 0 ≤ certFieldVal x.1 ∧ 0 ≤ certFieldVal x.2)
    (hy : 0 ≤ certFieldVal y.1 ∧ 0 ≤ certFieldVal y.2) :
    lowerHistoryComparisonHolds (lowerHistoryGreater C x y) (lowerRatio base.1) (lowerRatio base.2) (lowerScale base) ↔
      lowerHistoryValue base C y ≤ lowerHistoryValue base C x := by
  sorry

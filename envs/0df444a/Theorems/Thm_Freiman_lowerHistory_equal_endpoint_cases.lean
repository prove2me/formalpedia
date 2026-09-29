-- Prove2me | Theorems.Thm_Freiman_lowerHistory_equal_endpoint_cases
-- name    : Freiman.lowerHistory_equal_endpoint_cases
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:23:39.988726+00:00
-- url     : https://prove2.me/theorems/3cda0b16-d34a-49f5-b9e5-fd067b82d45a
-- title:
--   Freiman.lowerHistory_equal_endpoint_cases
-- statement:
--   Equal parity natural/auxiliary-shortening endpoint cases.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026); lower_core.tex, eq:lc-natural-tails and eq:lc-full-width; global_selection.tex, lem:global-suffix-targets; verification/families/target_selection/verify_h5_original_independent.py; role: source endpoint formulas

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic

open Freiman

theorem Freiman.lowerHistory_equal_endpoint_cases (hwidth : LowerHistoryWidthLaw) (hcf : ∀ (w : List ℕ+) (z : CertField), 0 ≤ certFieldVal z → certFieldVal (lowerHistoryCF w z) = prefixEval w (certFieldVal z))
    (base : LowerPair) (C : LowerHistoryContext) (hc : lowerHistoryContextFits base C) (words : LowerPair) (upper : Bool)
    (hp : lowerHistoryWordParity C words false = lowerHistoryWordParity C words true) :
    ∃ z cs, (z,cs) ∈ lowerHistoryEndpointCases C words upper ∧ lowerHistoryAtBase base cs ∧
      lowerHistoryEndpointReal base C words upper = lowerHistoryValue base C z := by
  sorry

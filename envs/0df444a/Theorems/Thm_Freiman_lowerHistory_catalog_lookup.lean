-- Prove2me | Theorems.Thm_Freiman_lowerHistory_catalog_lookup
-- name    : Freiman.lowerHistory_catalog_lookup
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:31:19.11061+00:00
-- url     : https://prove2.me/theorems/f7ec3c97-cfae-47f7-ab40-46e3dcae9dd4
-- title:
--   Freiman.lowerHistory_catalog_lookup
-- statement:
--   A generated descriptor has an actual catalog row; path IDs are metadata, not part of structural enumeration.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026); global_selection.tex, lem:global-suffix-targets; history_certificates.tex, app:all-suffix-histories; verification/families/target_selection/verify_suffix_targets_independent.py; certificates/target_selection/all_suffix_histories_printed.json; role: finite catalog coverage

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic

open Freiman

theorem Freiman.lowerHistory_catalog_lookup (hL : (lowerHistoryGeneratedKeys .left).toFinset = (lowerHistoryCatalogKeys .left).toFinset)
    (hR : (lowerHistoryGeneratedKeys .right).toFinset = (lowerHistoryCatalogKeys .right).toFinset)
    (hM : (lowerHistoryGeneratedKeys .mixed).toFinset = (lowerHistoryCatalogKeys .mixed).toFinset)
    (hX : (lowerHistoryGeneratedKeys .rightMixed).toFinset = (lowerHistoryCatalogKeys .rightMixed).toFinset)
    (hH : (lowerHistoryGeneratedKeys .initial).toFinset = (lowerHistoryCatalogKeys .initial).toFinset)
    (p : LowerHistoryPath) (hp : lowerHistoryPathKey p ∈ lowerHistoryGeneratedKeys p.catalog) :
    ∃ p2 ∈ lowerHistoryPaths.toList, lowerHistoryPathKey p2 = lowerHistoryPathKey p := by
  sorry

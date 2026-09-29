-- Prove2me | Theorems.Thm_Freiman_lowerHistory_catalog_X
-- name    : Freiman.lowerHistory_catalog_X
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:30:32.274982+00:00
-- url     : https://prove2.me/theorems/6a05620c-47bf-48e2-9137-700e4f61a27b
-- title:
--   Freiman.lowerHistory_catalog_X
-- statement:
--   Exact finite grammar coverage for the X catalog; initial H is separate from the four generic birth catalogs.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026); global_selection.tex, lem:global-suffix-targets; history_certificates.tex, app:all-suffix-histories; verification/families/target_selection/verify_suffix_targets_independent.py; certificates/target_selection/all_suffix_histories_printed.json; role: source independent history enumeration

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic

open Freiman

theorem Freiman.lowerHistory_catalog_X :
    (lowerHistoryGeneratedKeys .rightMixed).toFinset = (lowerHistoryCatalogKeys .rightMixed).toFinset := by
  sorry

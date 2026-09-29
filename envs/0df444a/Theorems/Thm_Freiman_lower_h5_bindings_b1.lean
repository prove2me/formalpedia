-- Prove2me | Theorems.Thm_Freiman_lower_h5_bindings_b1
-- name    : Freiman.lower_h5_bindings_b1
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:51:52.632754+00:00
-- url     : https://prove2.me/theorems/2fc31eac-fdbc-410d-ba48-63d24edf0bb5
-- title:
--   Freiman p97: bindings b1
-- statement:
--   Finite source replay for predecessor kind b1: exact context/parity, physical words, no narrow addition, source-cut DNF, each endpoint branch and its bound-pair witness. Only branch5 of the three exceptional B2 cases is retained for priority.
-- source:
--   Freiman report, 'The carried target in the shortened-left case of Section 14', sec:h5-source-target, Lemma lem:h5-original-two (source printed p. 97), report/source/staging/parts/h5_target.tex; global_selection.tex priority rule; certificates/target_selection/h5_cases.json and h5_original_appendix_printed.json; verification/families/target_selection/verify_h5_original_independent.py.

import Definitions.Def_Freiman_lowerH5Verification
import Definitions.Def_Freiman_lowerInitialEntry
import Mathlib.Tactic

open Freiman

theorem Freiman.lower_h5_bindings_b1 (hc : lowerH5CatalogValid) : ∀ c ∈ lowerH5Cases, c.kind = .b1 → lowerH5CaseBinding c := by
  sorry

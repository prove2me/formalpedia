-- Prove2me | Theorems.Thm_Freiman_lower_h5_witness_batch2
-- name    : Freiman.lower_h5_witness_batch2
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:52:32.952998+00:00
-- url     : https://prove2.me/theorems/fc7649cb-1d70-40d4-b1a2-3c0c7d59ab0d
-- title:
--   Freiman p97: witness batch2
-- statement:
--   Exact finite rational/field verification of stored source witnesses 19 through 36. Reuses certWitnessValid, including actual denominator signs, i+3*j coefficient order and strict/non-strict exclusion rules.
-- source:
--   Freiman report, 'The carried target in the shortened-left case of Section 14', sec:h5-source-target, Lemma lem:h5-original-two (source printed p. 97), report/source/staging/parts/h5_target.tex; global_selection.tex priority rule; certificates/target_selection/h5_cases.json and h5_original_appendix_printed.json; verification/families/target_selection/verify_h5_original_independent.py.

import Definitions.Def_Freiman_lowerH5Verification
import Definitions.Def_Freiman_lowerInitialEntry
import Mathlib.Tactic

open Freiman

theorem Freiman.lower_h5_witness_batch2 (i : ℕ) (hlo : 19 ≤ i) (hhi : i ≤ 36) : certWitnessValid (lowerH5Witness i) := by
  sorry

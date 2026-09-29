-- Prove2me | Theorems.Thm_Freiman_lower_h5_record_exclusion
-- name    : Freiman.lower_h5_record_exclusion
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:52:58.771434+00:00
-- url     : https://prove2.me/theorems/8395938b-33ed-411b-877d-54aa8ea10d94
-- title:
--   Freiman p97: record exclusion
-- statement:
--   Apply the already shared certificate soundness theorem to the two bound members of the actual record.
-- source:
--   Freiman report, 'The carried target in the shortened-left case of Section 14', sec:h5-source-target, Lemma lem:h5-original-two (source printed p. 97), report/source/staging/parts/h5_target.tex; global_selection.tex priority rule; certificates/target_selection/h5_cases.json and h5_original_appendix_printed.json; verification/families/target_selection/verify_h5_original_independent.py.

import Definitions.Def_Freiman_lowerH5Verification
import Definitions.Def_Freiman_lowerInitialEntry
import Mathlib.Tactic

open Freiman

theorem Freiman.lower_h5_record_exclusion (c : LowerH5Case) (record : LowerH5Record) (hb : LowerH5RecordBinding c record)
    (hw : certWitnessValid (lowerH5Witness record.witness)) (r s q : ℝ)
    (hr : certRectangleMem c.rectangle r s) (hs : lowerHistoryConditions (lowerH5RecordBounds record) r s q) : False := by
  sorry

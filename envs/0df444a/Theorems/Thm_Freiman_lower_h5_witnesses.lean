-- Prove2me | Theorems.Thm_Freiman_lower_h5_witnesses
-- name    : Freiman.lower_h5_witnesses
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:52:35.670135+00:00
-- url     : https://prove2.me/theorems/082a7458-8722-4e6e-b298-47dd7097554c
-- title:
--   Freiman p97: witnesses
-- statement:
--   Assemble the four finite witness ranges.
-- source:
--   Freiman report, 'The carried target in the shortened-left case of Section 14', sec:h5-source-target, Lemma lem:h5-original-two (source printed p. 97), report/source/staging/parts/h5_target.tex; global_selection.tex priority rule; certificates/target_selection/h5_cases.json and h5_original_appendix_printed.json; verification/families/target_selection/verify_h5_original_independent.py.

import Definitions.Def_Freiman_lowerH5Verification
import Definitions.Def_Freiman_lowerInitialEntry
import Mathlib.Tactic

open Freiman

theorem Freiman.lower_h5_witnesses : lowerH5AllWitnesses := by
  sorry

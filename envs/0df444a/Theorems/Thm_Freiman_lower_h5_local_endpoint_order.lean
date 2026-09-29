-- Prove2me | Theorems.Thm_Freiman_lower_h5_local_endpoint_order
-- name    : Freiman.lower_h5_local_endpoint_order
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:54:22.565562+00:00
-- url     : https://prove2.me/theorems/e025750f-c586-4cb1-b330-edd122d5d008
-- title:
--   Freiman p97: local endpoint order
-- statement:
--   Parity-aware transfer of the existing actual-cover endpoint order.
-- source:
--   Freiman report, 'The carried target in the shortened-left case of Section 14', sec:h5-source-target, Lemma lem:h5-original-two (source printed p. 97), report/source/staging/parts/h5_target.tex; global_selection.tex priority rule; certificates/target_selection/h5_cases.json and h5_original_appendix_printed.json; verification/families/target_selection/verify_h5_original_independent.py.

import Definitions.Def_Freiman_lowerH5Verification
import Definitions.Def_Freiman_lowerInitialEntry
import Mathlib.Tactic

open Freiman

theorem Freiman.lower_h5_local_endpoint_order (ho : ∀ p : LowerPair, lowerEndpoint p false ≤ lowerEndpoint p true)
    (p : LowerPair) (l : LowerLabel) : lowerLocalLower p l ≤ lowerH5LocalUpper p l := by
  sorry

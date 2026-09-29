-- Prove2me | Theorems.Thm_Freiman_lower_h5_initial_fixed
-- name    : Freiman.lower_h5_initial_fixed
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:52:49.220442+00:00
-- url     : https://prove2.me/theorems/3abb2fee-0db3-4c6b-b469-a968c296b42e
-- title:
--   Freiman p97: initial fixed
-- statement:
--   The 23 actual fixed roots have no mixed shortened-left state, checking both strict normalization possibilities without equal-width swap invariance.
-- source:
--   Freiman report, 'The carried target in the shortened-left case of Section 14', sec:h5-source-target, Lemma lem:h5-original-two (source printed p. 97), report/source/staging/parts/h5_target.tex; global_selection.tex priority rule; certificates/target_selection/h5_cases.json and h5_original_appendix_printed.json; verification/families/target_selection/verify_h5_original_independent.py.

import Definitions.Def_Freiman_lowerH5Verification
import Definitions.Def_Freiman_lowerInitialEntry
import Mathlib.Tactic

open Freiman

theorem Freiman.lower_h5_initial_fixed (p : LowerPair) (hp : p ∈ lowerFixedRoots) : ¬(lowerMixed p ∧ lowerL p) := by
  sorry

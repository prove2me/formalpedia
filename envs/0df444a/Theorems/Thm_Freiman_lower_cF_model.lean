-- Prove2me | Theorems.Thm_Freiman_lower_cF_model
-- name    : Freiman.lower_cF_model
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:14:56.583995+00:00
-- url     : https://prove2.me/theorems/381dfd97-72aa-4790-aee0-b1f57e62b215
-- title:
--   Freiman lower construction: cF model
-- statement:
--   The explicit two-sided period-S endpoint is admissible, has the seventh core, and has central value exactly cF using the existing cfValue.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, eq:lc-cF-word and eq:lc-cF-evaluation

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_cF_model : LowerModel lowerCFSequence ∧ localValue lowerCFSequence 0 = cF := by
  sorry

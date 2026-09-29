-- Prove2me | Theorems.Thm_Freiman_lower_run_parameters
-- name    : Freiman.lower_run_parameters
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:17:45.479958+00:00
-- url     : https://prove2.me/theorems/2739e040-4f2f-4cb1-8165-5a9f94170534
-- title:
--   Freiman lower construction: run parameters
-- statement:
--   (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hr : lowerRunOffered p) : lowerRunParameters p
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/j_family.tex, uniform parameter applicability

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_run_parameters (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hr : lowerRunOffered p) : lowerRunParameters p := by
  sorry

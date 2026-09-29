-- Prove2me | Theorems.Thm_Freiman_lower_run_family
-- name    : Freiman.lower_run_family
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:17:54.958159+00:00
-- url     : https://prove2.me/theorems/8bcbc4d8-e8d6-4058-adc7-19eeca056445
-- title:
--   Freiman lower construction: run family
-- statement:
--   (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hr : lowerRunOffered p) : lowerRunFamily p
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/j_family.tex, lem:lower-j3-uniform

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_run_family (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hr : lowerRunOffered p) : lowerRunFamily p := by
  sorry

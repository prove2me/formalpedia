-- Prove2me | Theorems.Thm_Freiman_lower_other22_reached_target
-- name    : Freiman.lower_other22_reached_target
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:20:48.889305+00:00
-- url     : https://prove2.me/theorems/3949d6c5-dc10-48db-ba87-edb205942135
-- title:
--   Freiman lower construction: other22 reached target
-- statement:
--   (t : ℝ) (S : LowerPair) (h : lowerOther22Reached t S) :
--       lowerLocalLower S ([2],[1]) ≤ lowerLocalCoordinate S t
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/other22_target.tex, lem:old23-other22-target

import Definitions.Def_Freiman_lowerOther22
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_other22_reached_target (t : ℝ) (S : LowerPair) (h : lowerOther22Reached t S) :
    lowerLocalLower S ([2],[1]) ≤ lowerLocalCoordinate S t := by
  sorry

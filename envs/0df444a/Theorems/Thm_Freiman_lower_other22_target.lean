-- Prove2me | Theorems.Thm_Freiman_lower_other22_target
-- name    : Freiman.lower_other22_target
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:20:33.524734+00:00
-- url     : https://prove2.me/theorems/ee88baf4-ed6b-437e-844a-8907fad71fc0
-- title:
--   Freiman lower construction: other22 target
-- statement:
--   (Z B R S : LowerPair) (h : LowerOther22Geometry Z B R S)
--       (t : ℝ) (ht : t ∈ lowerCover Z) (hp : lowerPriority t Z ([2],[3])) :
--       lowerLocalLower S ([2],[1]) ≤ lowerLocalCoordinate S t
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/other22_target.tex, lem:old23-other22-target

import Definitions.Def_Freiman_lowerOther22
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_other22_target (Z B R S : LowerPair) (h : LowerOther22Geometry Z B R S)
    (t : ℝ) (ht : t ∈ lowerCover Z) (hp : lowerPriority t Z ([2],[3])) :
    lowerLocalLower S ([2],[1]) ≤ lowerLocalCoordinate S t := by
  sorry

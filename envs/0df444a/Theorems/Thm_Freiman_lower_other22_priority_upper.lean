-- Prove2me | Theorems.Thm_Freiman_lower_other22_priority_upper
-- name    : Freiman.lower_other22_priority_upper
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:20:42.617897+00:00
-- url     : https://prove2.me/theorems/e81724df-eb16-4889-8c57-d68f10add00d
-- title:
--   Freiman lower construction: other22 priority upper
-- statement:
--   (Z B R S : LowerPair) (h : LowerOther22Geometry Z B R S)
--       (t : ℝ) (ht : t ∈ lowerCover Z) (hp : lowerPriority t Z ([2],[3]))
--       (hn : ¬ lowerEnds Z.1 [3,1]) : lowerChildUpper Z ([3],[2]) < lowerLocalCoordinate Z t
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/other22_target.tex, lem:old23-other22-target

import Definitions.Def_Freiman_lowerOther22
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_other22_priority_upper (Z B R S : LowerPair) (h : LowerOther22Geometry Z B R S)
    (t : ℝ) (ht : t ∈ lowerCover Z) (hp : lowerPriority t Z ([2],[3]))
    (hn : ¬ lowerEnds Z.1 [3,1]) : lowerChildUpper Z ([3],[2]) < lowerLocalCoordinate Z t := by
  sorry

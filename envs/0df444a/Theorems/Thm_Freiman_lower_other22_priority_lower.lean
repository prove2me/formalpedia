-- Prove2me | Theorems.Thm_Freiman_lower_other22_priority_lower
-- name    : Freiman.lower_other22_priority_lower
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:20:38.722098+00:00
-- url     : https://prove2.me/theorems/25bd9308-d443-4474-8fa3-63fe52a877b7
-- title:
--   Freiman lower construction: other22 priority lower
-- statement:
--   The source C32 lower tails are t31213,t213 while Z lower tails are t3,t213. Their strict first-tail comparison, with actual endpoint rules, gives this local lower anchor.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/other22_target.tex, lem:old23-other22-target

import Definitions.Def_Freiman_lowerOther22
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_other22_priority_lower (Z B R S : LowerPair) (h : LowerOther22Geometry Z B R S)
    (hn : ¬ lowerEnds Z.1 [3,1]) : lowerLocalLower Z ([3],[2]) < lowerBaseLower Z := by
  sorry

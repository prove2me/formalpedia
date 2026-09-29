-- Prove2me | Theorems.Thm_Freiman_lower_other22_parent_lower
-- name    : Freiman.lower_other22_parent_lower
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:20:27.223987+00:00
-- url     : https://prove2.me/theorems/0a4403a1-3ada-4f2a-a0b0-e1726ef119b0
-- title:
--   Freiman lower construction: other22 parent lower
-- statement:
--   Actual parent membership gives its lower endpoint in the normalized local scalar order.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/other22_target.tex, lem:old23-other22-target

import Definitions.Def_Freiman_lowerOther22
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_other22_parent_lower (Z : LowerPair) (t : ℝ) (ht : t ∈ lowerCover Z) : lowerBaseLower Z ≤ lowerLocalCoordinate Z t := by
  sorry

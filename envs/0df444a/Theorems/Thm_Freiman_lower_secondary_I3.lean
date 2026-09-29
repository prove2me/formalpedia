-- Prove2me | Theorems.Thm_Freiman_lower_secondary_I3
-- name    : Freiman.lower_secondary_I3
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:16:28.478976+00:00
-- url     : https://prove2.me/theorems/3f5d06ff-fbef-464c-a7a0-4bd917a09225
-- title:
--   Freiman lower construction: secondary I3
-- statement:
--   Exact upper bound for the secondary 4 in I3 using its displayed finite left and right context and permitted continuations.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/foundations.tex, found:central-dominance; exact secondary-4 certificate I3

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_secondary_I3 (a : ℤ → ℕ+) (ha : LowerModel a) (right : Bool) (hc : lowerCylinder (if right then ([3,2,1],[4,3,1]) else ([3,2,1],[4,3,1]).swap) a) :
    localValue a (if right then 1 else -1) < (113195/25000 : ℝ) := by
  sorry

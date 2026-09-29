-- Prove2me | Theorems.Thm_Freiman_lower_secondary_I7
-- name    : Freiman.lower_secondary_I7
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:16:22.923688+00:00
-- url     : https://prove2.me/theorems/6d33a8d0-3c29-40c8-9472-f6377519a567
-- title:
--   Freiman lower construction: secondary I7
-- statement:
--   Exact upper bound for the secondary 4 in I7 using its displayed finite left and right context and permitted continuations.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/foundations.tex, found:central-dominance; exact secondary-4 certificate I7

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_secondary_I7 (a : ℤ → ℕ+) (ha : LowerModel a) (right : Bool) (hc : lowerCylinder (if right then ([3,2,1,1,3],[4,3,2,2]) else ([3,2,1,1,3],[4,3,2,2]).swap) a) :
    localValue a (if right then 1 else -1) < (113195/25000 : ℝ) := by
  sorry

-- Prove2me | Theorems.Thm_Freiman_lower_secondary_I6
-- name    : Freiman.lower_secondary_I6
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:16:11.782274+00:00
-- url     : https://prove2.me/theorems/936b1d8b-81d4-4139-b827-5d2de77911a6
-- title:
--   Freiman lower construction: secondary I6
-- statement:
--   Exact upper bound for the secondary 4 in I6 using its displayed finite left and right context and permitted continuations.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/foundations.tex, found:central-dominance; exact secondary-4 certificate I6

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_secondary_I6 (a : ℤ → ℕ+) (ha : LowerModel a) (right : Bool) (hc : lowerCylinder (if right then ([3,2,1,1,3],[4,3,2,3]) else ([3,2,1,1,3],[4,3,2,3]).swap) a) :
    localValue a (if right then 1 else -1) < (113195/25000 : ℝ) := by
  sorry

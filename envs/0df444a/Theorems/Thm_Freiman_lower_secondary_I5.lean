-- Prove2me | Theorems.Thm_Freiman_lower_secondary_I5
-- name    : Freiman.lower_secondary_I5
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:16:16.143993+00:00
-- url     : https://prove2.me/theorems/7f12f8e9-27ef-4fbf-be3e-dbea8d04d80d
-- title:
--   Freiman lower construction: secondary I5
-- statement:
--   Exact upper bound for the secondary 4 in I5 using its displayed finite left and right context and permitted continuations.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/foundations.tex, found:central-dominance; exact secondary-4 certificate I5

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_secondary_I5 (a : ℤ → ℕ+) (ha : LowerModel a) (right : Bool) (hc : lowerCylinder (if right then ([3,2,1,1,2],[4,3,2,2]) else ([3,2,1,1,2],[4,3,2,2]).swap) a) :
    localValue a (if right then 1 else -1) < (113195/25000 : ℝ) := by
  sorry

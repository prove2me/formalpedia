-- Prove2me | Theorems.Thm_Freiman_lower_cylinder_reflection
-- name    : Freiman.lower_cylinder_reflection
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:18:07.383146+00:00
-- url     : https://prove2.me/theorems/568d30a7-7595-426c-a63b-4e2d29d1574d
-- title:
--   Freiman lower construction: cylinder reflection
-- statement:
--   A word in the reflected physical cylinder becomes a word in the incoming ordered cylinder after negating integer coordinates.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, reflection of physical cylinders

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_cylinder_reflection (p : LowerPair) (a : ℤ → ℕ+) (hc : lowerCylinder p.swap a) :
    lowerCylinder p (fun i : ℤ => a (-i)) := by
  sorry

-- Prove2me | Theorems.Thm_Freiman_lower_cylinder_distance
-- name    : Freiman.lower_cylinder_distance
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:17:37.647209+00:00
-- url     : https://prove2.me/theorems/7bed5596-405b-4c3c-839f-d4c77a069830
-- title:
--   Freiman lower construction: cylinder distance
-- statement:
--   (p : LowerPair) (a b : ℤ → ℕ+) (ha : lowerCylinder p a) (hb : lowerCylinder p b) :
--       |localValue a 0 - localValue b 0| ≤ lowerCylinderError p
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/foundations.tex, found:continuity; lower_core.tex, physical cylinder limit

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_cylinder_distance (p : LowerPair) (a b : ℤ → ℕ+) (ha : lowerCylinder p a) (hb : lowerCylinder p b) :
    |localValue a 0 - localValue b 0| ≤ lowerCylinderError p := by
  sorry

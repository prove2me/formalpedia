-- Prove2me | Theorems.Thm_Freiman_lower_cover_distance
-- name    : Freiman.lower_cover_distance
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:16:00.756238+00:00
-- url     : https://prove2.me/theorems/c745f000-1cec-48c8-8a8e-4e7eb04f3deb
-- title:
--   Freiman lower construction: cover distance
-- statement:
--   (p : LowerPair) (hp : lowerAdmissible p) (a : ℤ → ℕ+)
--       (ha : LowerModel a) (hc : lowerCylinder p a) (t : ℝ) (ht : t ∈ lowerCover p) :
--       |localValue a 0 - t| ≤ lowerCylinderError p
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, lem:lc-target-limit

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_cover_distance (p : LowerPair) (hp : lowerAdmissible p) (a : ℤ → ℕ+)
    (ha : LowerModel a) (hc : lowerCylinder p a) (t : ℝ) (ht : t ∈ lowerCover p) :
    |localValue a 0 - t| ≤ lowerCylinderError p := by
  sorry

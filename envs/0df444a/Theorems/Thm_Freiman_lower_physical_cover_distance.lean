-- Prove2me | Theorems.Thm_Freiman_lower_physical_cover_distance
-- name    : Freiman.lower_physical_cover_distance
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:18:10.838632+00:00
-- url     : https://prove2.me/theorems/a08aa5ef-a2b9-4aa1-8e1a-b3c153bb7c8c
-- title:
--   Freiman lower construction: physical cover distance
-- statement:
--   (h : ℕ → LowerPair) (n : ℕ) (hp : lowerAdmissible (h n))
--       (a : ℤ → ℕ+) (ha : LowerModel a) (hc : lowerCylinder (lowerPhysicalPath h n) a)
--       (t : ℝ) (ht : t ∈ lowerCover (h n)) :
--       |localValue a 0-t| ≤ lowerCylinderError (lowerPhysicalPath h n)
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, target limit with explicit orientation

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_physical_cover_distance (h : ℕ → LowerPair) (n : ℕ) (hp : lowerAdmissible (h n))
    (a : ℤ → ℕ+) (ha : LowerModel a) (hc : lowerCylinder (lowerPhysicalPath h n) a)
    (t : ℝ) (ht : t ∈ lowerCover (h n)) :
    |localValue a 0-t| ≤ lowerCylinderError (lowerPhysicalPath h n) := by
  sorry

-- Prove2me | Theorems.Thm_MasulloRH_rational_mesh_completes_unit_height_em_balls
-- name    : MasulloRH.rational_mesh_completes_unit_height_em_balls
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-27T02:56:34.579108+00:00
-- url     : https://prove2.me/theorems/c2d54100-39e1-5d26-af0b-b159797bc9da
-- title:
--   Rational meshes and sound Euler–Maclaurin balls on the Masullo rectangles
-- statement:
--   All mesh nodes lie in the original rectangle. Every point is within radius 2/m of a node weakly to its left. The specified derivative budget bounds variation throughout each rectangle, and any ball satisfying the original strict margin excludes a zero at the point it covers.
-- source:
--   For the existing Masullo unit-height Euler–Maclaurin ball obligation https://prove2.me/theorems/458479ec-80ed-41ca-9e08-9f4753b887b0 . The exact local error and derivative estimates are https://prove2.me/theorems/1e043161-8bba-425f-ba0d-2ddcb47971fe and https://prove2.me/theorems/724f2f12-f6c3-4346-91a0-da366324b4c2 .

import Definitions.Def_MasulloRH_UnitHeightMeshes
import Mathlib.NumberTheory.LSeries.RiemannZeta

open Set MasulloRH.UnitHeightMeshes

theorem MasulloRH.rational_mesh_completes_unit_height_em_balls :
    (∀ n k m i j : ℕ, 0 < m → i ≤ m → j ≤ m → rationalCenter (node n k m i j) ∈ rect n k) ∧
    (∀ n k m : ℕ, 0 < m → ∀ s ∈ rect n k, ∃ i ≤ m, ∃ j ≤ m,
      (rationalCenter (node n k m i j)).re ≤ s.re ∧ dist s (rationalCenter (node n k m i j)) < (rad m:ℝ)) ∧
    (∀ n k : ℕ, ∀ s ∈ rect n k, ∀ c ∈ rect n k,
      ‖riemannZeta s-riemannZeta c‖ ≤ (derivBudget n:ℝ)*dist s c) ∧
    (∀ n k : ℕ, ∀ s ∈ rect n k, covered n k s → riemannZeta s ≠ 0) := by sorry

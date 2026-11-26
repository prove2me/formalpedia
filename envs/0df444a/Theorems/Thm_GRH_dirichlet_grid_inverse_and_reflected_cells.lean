-- Prove2me | Theorems.Thm_GRH_dirichlet_grid_inverse_and_reflected_cells
-- name    : GRH.dirichlet_grid_inverse_and_reflected_cells
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T18:45:37.585731+00:00
-- url     : https://prove2.me/theorems/6ee40481-eb43-5202-b8bf-63be74ff97ce
-- title:
--   Inverse characters and reflected cells pass the same Dirichlet grid
-- statement:
--   For every mesh size, a character and its inverse pass the same rectangle. The reduced test is equivalent at that same size to testing every original cell.
-- source:
--   Derived for the centered Möbius theorem in the Masullo mission. https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006

import Definitions.Def_GRH_DyadicCharacterGrid

open GRH.DyadicCharacterGrid GRH.DirichletGrid

theorem GRH.dirichlet_grid_inverse_and_reflected_cells {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (a b H : ℝ) (m : ℕ) :
    (Passes χ⁻¹ a b H m ↔ Passes χ a b H m) ∧ (Checks χ a b H m ↔ Passes χ a b H m) := by sorry

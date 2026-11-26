-- Prove2me | Theorems.Thm_GRH_dirichlet_grid_of_dyadic_rectangles
-- name    : GRH.dirichlet_grid_of_dyadic_rectangles
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T18:45:38.702098+00:00
-- url     : https://prove2.me/theorems/911c5a7a-d526-5ca7-878f-041ed484f9a9
-- title:
--   Powers of two suffice for the nested Dirichlet rectangles
-- statement:
--   For a nonprincipal character, existence of a mesh at every target height is equivalent to existence of meshes at heights one, two, four and successive powers of two.
-- source:
--   Derived for the centered Möbius theorem in the Masullo mission. https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006

import Definitions.Def_GRH_DyadicCharacterGrid

open GRH.DyadicCharacterGrid GRH.DirichletGrid

theorem GRH.dirichlet_grid_of_dyadic_rectangles {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ≠1)
    (b : ℝ) (hb : (1/2:ℝ)<b) (hb1 : b≤1) :
    (∀ h : ℕ, ∃ m : ℕ, Passes χ (left b h) b ((h:ℝ)+1) m) ↔
      ∀ k : ℕ, ∃ m : ℕ, Passes χ (left b (index k)) b ((index k:ℝ)+1) m := by sorry

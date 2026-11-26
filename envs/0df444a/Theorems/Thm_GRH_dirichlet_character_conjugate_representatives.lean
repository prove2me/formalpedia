-- Prove2me | Theorems.Thm_GRH_dirichlet_character_conjugate_representatives
-- name    : GRH.dirichlet_character_conjugate_representatives
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T18:45:43.218565+00:00
-- url     : https://prove2.me/theorems/1798c11f-54d1-4350-8a69-cf086c43d3b8
-- title:
--   A representative of each conjugate pair of Dirichlet characters
-- statement:
--   Every character or its inverse has positive imaginary part at its first nonreal residue, or has entirely real values. Both are selected exactly when the character is self-inverse.
-- source:
--   Derived for the centered Möbius theorem in the Masullo mission. https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006

import Definitions.Def_GRH_DyadicCharacterGrid

open GRH.DyadicCharacterGrid GRH.DirichletGrid

theorem GRH.dirichlet_character_conjugate_representatives {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    (Oriented χ ∨ Oriented χ⁻¹) ∧ ((Oriented χ ∧ Oriented χ⁻¹) ↔ χ=χ⁻¹) := by sorry

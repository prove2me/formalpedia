-- Prove2me | Theorems.Thm_GRH_character_moment_first_and_covered_grids
-- name    : GRH.character_moment_first_and_covered_grids
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T17:22:02.740612+00:00
-- url     : https://prove2.me/theorems/ae3c0b21-b543-40e9-a9bd-642859cc875c
-- title:
--   The first Dirichlet grid at conductors 11 and 13 and every grid certified by convolution moments
-- statement:
--   For every nonprincipal character the specified finite Dirichlet-polynomial grid exists on the first target line for every modulus dividing 66 or 78. At any height it exists whenever the arithmetic moment certificate covers the corresponding target rectangle.
-- source:
--   Developed for the centered Möbius theorem at https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006 and its open primitive grid condition at https://prove2.me/theorems/1b3886ba-6475-4979-b196-63418759603e. Uses the centered Abel estimate at https://prove2.me/theorems/3b5a3db7-3b41-46b5-a41d-4a78754ad8d2 and the power variation estimate at https://prove2.me/theorems/189b3afb-17f1-43b4-9047-0e36a164d965.

import Definitions.Def_GRH_CharacterMoment
import Definitions.Def_GRH_DirichletGrid

open GRH.DirichletGrid

theorem GRH.character_moment_first_and_covered_grids (d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d) (hχ : χ ≠ 1)
    (h : ℕ) (hp : (h=0 ∧ (d ∣ 66 ∨ d ∣ 78)) ∨ GRH.CharacterMoment.Covers d
      (1/2+((0.8749570698:ℝ)-1/2)/((h:ℝ)+1)) (0.8749570698:ℝ) ((h:ℝ)+1)) :
    ∃ m : ℕ, Passes χ (1/2+((0.8749570698:ℝ)-1/2)/((h:ℝ)+1))
      (0.8749570698:ℝ) ((h:ℝ)+1) m := by sorry

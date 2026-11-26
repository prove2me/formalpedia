-- Prove2me | Theorems.Thm_GRH_primitive_dirichlet_grids_outside_character_moments
-- name    : GRH.primitive_dirichlet_grids_outside_character_moments
-- status  : Open
-- author  : @scuba8684
-- created : 2026-11-26T17:22:10.289279+00:00
-- url     : https://prove2.me/theorems/dd0e053a-d042-4f4a-80d9-5e7a0bcc4ee8
-- title:
--   Primitive Dirichlet grids remaining outside the initial-gap, unit-count and convolution tests
-- statement:
--   For every primitive nonprincipal character, supply a finite Dirichlet-polynomial grid at each target height and conductor where the initial-gap test, the weighted unit-count test, and the centered convolution test all fail.
-- source:
--   Developed for the centered Möbius theorem at https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006 and its open primitive grid condition at https://prove2.me/theorems/1b3886ba-6475-4979-b196-63418759603e. Uses the centered Abel estimate at https://prove2.me/theorems/3b5a3db7-3b41-46b5-a41d-4a78754ad8d2 and the power variation estimate at https://prove2.me/theorems/189b3afb-17f1-43b4-9047-0e36a164d965.

import Definitions.Def_GRH_DirichletGrid
import Definitions.Def_GRH_DirichletPeriod
import Definitions.Def_GRH_CharacterMoment

theorem GRH.primitive_dirichlet_grids_outside_character_moments
    (d : ℕ) [NeZero d] (ψ : DirichletCharacter ℂ d) (hprim : ψ.IsPrimitive) (hψ : ψ ≠ 1)
    (h : ℕ) (hgap : ¬ GRH.DirichletPeriod.Covers d
      (1/2 + ((0.8749570698:ℝ)-1/2)/((h:ℝ)+1)) ((h:ℝ)+1))
    (hweight : ¬ GRH.DirichletPrefix.Covers d
      (1/2 + ((0.8749570698:ℝ)-1/2)/((h:ℝ)+1)) (0.8749570698:ℝ) ((h:ℝ)+1))
    (hmoment : ¬ GRH.CharacterMoment.Covers d
      (1/2 + ((0.8749570698:ℝ)-1/2)/((h:ℝ)+1)) (0.8749570698:ℝ) ((h:ℝ)+1)) :
    ∃ m : ℕ, GRH.DirichletGrid.Passes ψ
      (1/2 + ((0.8749570698:ℝ)-1/2)/((h:ℝ)+1)) (0.8749570698:ℝ) ((h:ℝ)+1) m := by sorry

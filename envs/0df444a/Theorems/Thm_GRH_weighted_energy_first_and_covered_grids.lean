-- Prove2me | Theorems.Thm_GRH_weighted_energy_first_and_covered_grids
-- name    : GRH.weighted_energy_first_and_covered_grids
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T18:07:26.941357+00:00
-- url     : https://prove2.me/theorems/1b1da4d6-66cd-4891-960c-a2298ab94ac3
-- title:
--   The first primitive grids at conductors 17 and 19 and all weighted energy grids
-- statement:
--   The first finite grid holds for every nonprincipal character at divisors of 102 and 114. The same conclusion holds at any target height where a weighted energy certificate passes.
-- source:
--   Derived for the centered Möbius theorem in the Masullo mission. https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006

import Definitions.Def_GRH_WeightedEnergy
import Definitions.Def_GRH_DirichletGrid

open GRH.DirichletGrid

theorem GRH.weighted_energy_first_and_covered_grids (d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d) (hχ : χ ≠ 1)
    (h : ℕ) (hp : (h=0 ∧ (d ∣ 102 ∨ d ∣ 114)) ∨ GRH.WeightedEnergy.Covers d
      (1/2+((0.8749570698:ℝ)-1/2)/((h:ℝ)+1)) (0.8749570698:ℝ) ((h:ℝ)+1)) :
    ∃ m : ℕ, Passes χ (1/2+((0.8749570698:ℝ)-1/2)/((h:ℝ)+1))
      (0.8749570698:ℝ) ((h:ℝ)+1) m := by sorry

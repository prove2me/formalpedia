-- Prove2me | Theorems.Thm_MasulloRH_height_two_exterior_energy_bounds
-- name    : MasulloRH.height_two_exterior_energy_bounds
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T11:26:04.248226+00:00
-- url     : https://prove2.me/theorems/477003ff-b7e5-59d8-92da-f439380fe3da
-- title:
--   A uniform energy bound for the 6,144 exterior cells of the height-two grid
-- statement:
--   For cell indices \(0\le j<5120\) or \(64512\le j<65536\), the rational upper energy per cell is at most \(2^{-110}\). Each of the 80 leftmost and 16 rightmost blocks of 64 cells meets its published budget. The sum of the energy terms over those two ranges is at most \(3/2^{99}\).
-- source:
--   The exact rational energy terms are defined at https://prove2.me/definitions/b3a30ca4-39cc-42b4-af9e-c419ffe83506 and the dyadic block budgets at https://prove2.me/definitions/b51ff300-07ee-48f0-baf1-91a12f1bfd5a. The previous grid decomposition is https://prove2.me/submissions/7b92c99f-46a8-43a3-8b78-7deb34ec8686. This statement refines https://prove2.me/theorems/7ffa130f-1647-4b70-99fe-8a6da1ff2813.

import Definitions.Def_MasulloRH_HeightTwoComputedGrid
import Definitions.Def_MasulloRH_HeightTwoBlockBudgets

open MasulloRH.ComputedGrid MasulloRH.BlockBudgets
open scoped BigOperators
set_option autoImplicit false

theorem MasulloRH.height_two_exterior_energy_bounds :
    (∀ j : ℕ, j < 65536 → (j < 5120 ∨ 64512 ≤ j) →
        energyTerm j ≤ 1 / (2 : ℚ)^110) ∧
    (∀ b ∈ Finset.range 1024, (b < 80 ∨ 1008 ≤ b) →
        (∑ j ∈ Finset.range 64, energyTerm (b * 64 + j)) ≤ cap b) ∧
    (∑ j ∈ Finset.range 5120, energyTerm j) +
        (∑ j ∈ Finset.range 1024, energyTerm (64512 + j)) ≤ 3 / (2 : ℚ)^99 := by sorry

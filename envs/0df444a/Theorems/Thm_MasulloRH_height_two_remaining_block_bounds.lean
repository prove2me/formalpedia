-- Prove2me | Theorems.Thm_MasulloRH_height_two_remaining_block_bounds
-- name    : MasulloRH.height_two_remaining_block_bounds
-- status  : Open
-- author  : @scuba8684
-- created : 2026-11-26T10:42:17.985375+00:00
-- url     : https://prove2.me/theorems/7ffa130f-1647-4b70-99fe-8a6da1ff2813
-- title:
--   Remaining local energy inequalities for the deterministic height-two table
-- statement:
--   For each of the 1,024 blocks other than block 512, sum the 64 exact rational energy entries at indices \(64b\) through \(64b+63\). This sum is at most the corresponding integer budget times \(2^{-40}\). Block 512 covers the interval starting at zero and has a separate kernel calculation. Together the 1,023 local inequalities finish the global budget.
-- source:
--   A quantitative certificate for https://prove2.me/theorems/9921bc57-a605-47ac-a7be-76ddbcc1c2e4 using the deterministic table https://prove2.me/definitions/b3a30ca4-39cc-42b4-af9e-c419ffe83506 .

import Definitions.Def_MasulloRH_HeightTwoComputedGrid
import Definitions.Def_MasulloRH_HeightTwoBlockBudgets

open MasulloRH.ComputedGrid MasulloRH.BlockBudgets
open scoped BigOperators
set_option autoImplicit false

theorem MasulloRH.height_two_remaining_block_bounds :
    ∀ b ∈ Finset.range 1024, b ≠ 512 →
      (∑ j ∈ Finset.range 64, energyTerm (b*64+j)) ≤ cap b := by sorry

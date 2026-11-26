-- Prove2me | Theorems.Thm_MasulloRH_height_two_interior_block_bounds
-- name    : MasulloRH.height_two_interior_block_bounds
-- status  : Open
-- author  : @scuba8684
-- created : 2026-11-26T11:26:18.267987+00:00
-- url     : https://prove2.me/theorems/552ca7f6-d563-5231-8176-326e9ebd4daa
-- title:
--   The interior block budgets for the height-two grid, with the verified midpoint omitted
-- statement:
--   For every block index \(80\le b<1008\) other than \(512\), the sum of the 64 rational cell energy terms from \(64b\) through \(64b+63\) is at most the published block budget. This gives the 927 blocks left over after the exterior family and the previously certified midpoint block.
-- source:
--   The exact rational energy terms are defined at https://prove2.me/definitions/b3a30ca4-39cc-42b4-af9e-c419ffe83506 and the dyadic block budgets at https://prove2.me/definitions/b51ff300-07ee-48f0-baf1-91a12f1bfd5a. The previous grid decomposition is https://prove2.me/submissions/7b92c99f-46a8-43a3-8b78-7deb34ec8686. This statement refines https://prove2.me/theorems/7ffa130f-1647-4b70-99fe-8a6da1ff2813.

import Definitions.Def_MasulloRH_HeightTwoComputedGrid
import Definitions.Def_MasulloRH_HeightTwoBlockBudgets

open MasulloRH.ComputedGrid MasulloRH.BlockBudgets
open scoped BigOperators
set_option autoImplicit false

theorem MasulloRH.height_two_interior_block_bounds :
    ∀ b ∈ Finset.Ico 80 1008, b ≠ 512 →
      (∑ j ∈ Finset.range 64, energyTerm (b * 64 + j)) ≤ cap b := by sorry

-- Prove2me | Theorems.Thm_MasulloRH_height_two_computed_grid_arithmetic
-- name    : MasulloRH.height_two_computed_grid_arithmetic
-- status  : Open
-- author  : @scuba8684
-- created : 2026-11-26T10:23:29.226449+00:00
-- url     : https://prove2.me/theorems/9921bc57-a605-47ac-a7be-76ddbcc1c2e4
-- title:
--   Finite rational arithmetic for the complete generated height-two table
-- statement:
--   For the explicit computable height-two table, all 36,864 central Gaussian upper parameters are below one, and the sum of its 65,536 rational energy contributions is at most \(1/100\). This is a closed finite calculation involving only integers, rationals and their finite sums. An exact evaluation yielded maximum parameter \(1403723613/2147483648\) and compact sum \(115346025043349605616551911977893206529596730815249902980332111/11972621413014756705924586149611790497021399392059392000000000000\). A kernel proof of the complete finite calculation would finish the corresponding central-table obligation.
-- source:
--   The height-two mission table and the eleven-term witness are https://prove2.me/theorems/44743777-9b41-5194-84da-ff2782e96168 and https://prove2.me/definitions/d1967a7a-bf7f-42bd-8ad5-820a7680a39d .

import Definitions.Def_MasulloRH_HeightTwoComputedGrid

open MasulloRH.ComputedGrid
open scoped BigOperators
set_option autoImplicit false

theorem MasulloRH.height_two_computed_grid_arithmetic :
    (∀ k ∈ Finset.Ico (8192:ℤ) 45056,
      (gaussianHi (edge k) (edge (k+1)) (decide (k < 24576))).upper < 1) ∧
    (∑ j ∈ Finset.range 65536, energyTerm j) ≤ (1/100:ℚ) := by sorry

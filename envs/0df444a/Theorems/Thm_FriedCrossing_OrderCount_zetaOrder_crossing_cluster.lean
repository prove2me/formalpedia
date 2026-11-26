-- Prove2me | Theorems.Thm_FriedCrossing_OrderCount_zetaOrder_crossing_cluster
-- name    : FriedCrossing.OrderCount.zetaOrder_crossing_cluster
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:54:40.163501+00:00
-- url     : https://prove2.me/theorems/9b697f3e-2c22-578e-ba06-5374a9629d7c
-- title:
--   Order Count: zeta Order crossing cluster
-- statement:
--   The generic crossing cluster (0,1,2,1,0): order 0, ζ regular at 0.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_9_03.lean#L152-L152
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_9_03.lean#L152-L152

import Definitions.Def_B1s_fried_statement_defs_9_14
import Definitions.Def_B1s_fried_crossing_9_03
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.OrderCount
variable {K : Type*} [Field K] {V₁ V₂ V₃ : Type*}
  [AddCommGroup V₁] [Module K V₁] [FiniteDimensional K V₁]
  [AddCommGroup V₂] [Module K V₂] [FiniteDimensional K V₂]
  [AddCommGroup V₃] [Module K V₃]

theorem FriedCrossing.OrderCount.zetaOrder_crossing_cluster : zetaOrder ![0, 1, 2, 1, 0] = 0 := by sorry

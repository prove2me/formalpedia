-- Prove2me | Theorems.Thm_FriedCrossing_OrderCount_zetaOrder_pole_chain
-- name    : FriedCrossing.OrderCount.zetaOrder_pole_chain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:54:53.403973+00:00
-- url     : https://prove2.me/theorems/e764881c-1d80-4707-b350-1f05ceb114ed
-- title:
--   Order Count: zeta Order pole chain
-- statement:
--   The (1,1,1) chain headed by the non-closed 1-form: a simple POLE.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_9_03.lean#L146-L146
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_9_03.lean#L146-L146

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

theorem FriedCrossing.OrderCount.zetaOrder_pole_chain : zetaOrder ![0, 1, 1, 1, 0] = -1 := by sorry

-- Prove2me | Theorems.Thm_FriedCrossing_OrderCount_zetaOrder_eq
-- name    : FriedCrossing.OrderCount.zetaOrder_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:44:34.260744+00:00
-- url     : https://prove2.me/theorems/252c336d-fab1-4f4e-bad5-4a448a5b551c
-- title:
--   Order Count: zeta Order eq
-- statement:
--   With c₀ = c₄ = 0 (DGRS Lemma 7.4 + ⋆) and c₃ = c₁ (⋆): m = c₂ − 2c₁.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_9_03.lean#L139-L143
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_9_03.lean#L139-L143

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

theorem FriedCrossing.OrderCount.zetaOrder_eq (c : Fin 5 → ℕ) (h0 : c 0 = 0) (h4 : c 4 = 0) (h31 : c 3 = c 1) :
    zetaOrder c = (c 2 : ℤ) - 2 * c 1 := by sorry

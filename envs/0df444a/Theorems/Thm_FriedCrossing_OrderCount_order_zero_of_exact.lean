-- Prove2me | Theorems.Thm_FriedCrossing_OrderCount_order_zero_of_exact
-- name    : FriedCrossing.OrderCount.order_zero_of_exact
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T04:44:21.082406+00:00
-- url     : https://prove2.me/theorems/83041b84-d1df-5386-9266-429d4597b5e8
-- title:
--   Order Count: order zero of exact
-- statement:
--   P2: exact reduced complex + duality ⇒ c₂ = 2c₁ ⇒ the ζ-order at 0 is 0.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_9_03.lean#L155-L168
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_9_03.lean#L155-L168

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

theorem FriedCrossing.OrderCount.order_zero_of_exact (f : V₁ →ₗ[K] V₂) (g : V₂ →ₗ[K] V₃)
    (hf : Function.Injective f) (hfg : LinearMap.range f = LinearMap.ker g)
    (hg : Function.Surjective g) (c : Fin 5 → ℕ) (hacyc : c 0 = 0 ∧ c 4 = 0)
    (hdual : c 3 = c 1)
    (hdims : c 1 = Module.finrank K V₁ ∧ c 2 = Module.finrank K V₂ ∧
      c 3 = Module.finrank K V₃) :
    zetaOrder c = 0 := by sorry

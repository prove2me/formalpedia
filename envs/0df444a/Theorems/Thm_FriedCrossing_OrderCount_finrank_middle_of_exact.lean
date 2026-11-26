-- Prove2me | Theorems.Thm_FriedCrossing_OrderCount_finrank_middle_of_exact
-- name    : FriedCrossing.OrderCount.finrank_middle_of_exact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:38:32.132146+00:00
-- url     : https://prove2.me/theorems/90b540a9-ba37-5219-bdaf-52e52a9841be
-- title:
--   Order Count: finrank middle of exact
-- statement:
--   Rank–nullity twice: for an exact 0 → V₁ → V₂ → V₃ → 0,
--   dim V₂ = dim V₁ + dim V₃.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_9_03.lean#L128-L136
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_9_03.lean#L128-L136

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

theorem FriedCrossing.OrderCount.finrank_middle_of_exact (f : V₁ →ₗ[K] V₂) (g : V₂ →ₗ[K] V₃)
    (hf : Function.Injective f) (hfg : LinearMap.range f = LinearMap.ker g)
    (hg : Function.Surjective g) :
    Module.finrank K V₂ = Module.finrank K V₁ + Module.finrank K V₃ := by sorry

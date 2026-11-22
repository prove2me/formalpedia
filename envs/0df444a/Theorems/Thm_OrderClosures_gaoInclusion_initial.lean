-- Prove2me | Theorems.Thm_OrderClosures_gaoInclusion_initial
-- name    : OrderClosures.gaoInclusion_initial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:05:11.312464+00:00
-- url     : https://prove2.me/theorems/056284e0-4158-41b1-aacb-2eb6dfaff9b4
-- title:
--   Order Closures: gao Inclusion initial
-- statement:
--   Proves the initial inclusion of a component Gao stage into the global
--   solid set; used as the base case of `gaoInclusion_stage`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/Iterations.lean#L371-L402
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/Iterations.lean#L371-L402

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_StageFormula
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_Iterations
set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v

theorem OrderClosures.gaoInclusion_initial
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    (β : GaoComponentIndex κ) :
    gaoProductInclusion κ β '' GaoStageSet β.1 1 ⊆ gaoIterationSet κ hκ := by sorry

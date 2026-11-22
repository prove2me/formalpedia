-- Prove2me | Theorems.Thm_OrderClosures_gaoIterationProduct_abs_snd
-- name    : OrderClosures.gaoIterationProduct_abs_snd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:04:54.548622+00:00
-- url     : https://prove2.me/theorems/40e4e657-be1d-4898-946b-68c51c84068a
-- title:
--   Order Closures: gao Iteration Product abs snd
-- statement:
--   Computes absolute value in the padding coordinate of the iteration
--   product; used to recover generator indices from domination.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/Iterations.lean#L95-L98
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/Iterations.lean#L95-L98

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

theorem OrderClosures.gaoIterationProduct_abs_snd
    (κ : Cardinal.{u}) (x : GaoIterationProduct κ)
    (a : ULift.{u + 1, u} (Cardinal.ord κ).ToType) :
    |x|.2 a = |x.2 a| := by sorry

-- Prove2me | Theorems.Thm_OrderClosures_gaoIterationProduct_abs_fst
-- name    : OrderClosures.gaoIterationProduct_abs_fst
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:04:45.000929+00:00
-- url     : https://prove2.me/theorems/62cee446-91ae-4aee-97a2-a74407824dda
-- title:
--   Order Closures: gao Iteration Product abs fst
-- statement:
--   Computes absolute value in the component part of the iteration product;
--   used to analyze solid domination of global generators.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/Iterations.lean#L89-L91
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/Iterations.lean#L89-L91

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

theorem OrderClosures.gaoIterationProduct_abs_fst
    (κ : Cardinal.{u}) (x : GaoIterationProduct κ) (β : GaoComponentIndex κ) :
    |x|.1 β = |x.1 β| := by sorry

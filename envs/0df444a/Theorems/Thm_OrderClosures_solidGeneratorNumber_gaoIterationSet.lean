-- Prove2me | Theorems.Thm_OrderClosures_solidGeneratorNumber_gaoIterationSet
-- name    : OrderClosures.solidGeneratorNumber_gaoIterationSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:05:21.574508+00:00
-- url     : https://prove2.me/theorems/73937853-6cd5-47bd-aaea-3652e4af6616
-- title:
--   Order Closures: solid Generator Number gao Iteration Set
-- statement:
--   Proves that the constructed solid set has generator number exactly `κ`;
--   used in the final arbitrary-iteration theorem.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/Iterations.lean#L568-L621
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/Iterations.lean#L568-L621

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

theorem OrderClosures.solidGeneratorNumber_gaoIterationSet
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ) :
    solidGeneratorNumber (gaoIterationSet κ hκ) = Cardinal.lift.{u + 1, u} κ := by sorry

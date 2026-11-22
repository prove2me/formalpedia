-- Prove2me | Theorems.Thm_OrderClosures_gaoGlobalGenerator_index_eq_of_abs_le
-- name    : OrderClosures.gaoGlobalGenerator_index_eq_of_abs_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:04:38.002519+00:00
-- url     : https://prove2.me/theorems/f592c0fc-ecf3-44ad-8b89-522b7abc1cbd
-- title:
--   Order Closures: gao Global Generator index eq of abs le
-- statement:
--   Recovers equality of generator indices from solid domination; used to
--   prove injectivity of the global generator map.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/Iterations.lean#L530-L540
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/Iterations.lean#L530-L540

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

theorem OrderClosures.gaoGlobalGenerator_index_eq_of_abs_le
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    {a b : ULift.{u + 1, u} (Cardinal.ord κ).ToType}
    (hab : |gaoGlobalGenerator κ hκ a| ≤ |gaoGlobalGenerator κ hκ b|) :
    a = b := by sorry

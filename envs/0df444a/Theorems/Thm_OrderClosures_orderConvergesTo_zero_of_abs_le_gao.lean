-- Prove2me | Theorems.Thm_OrderClosures_orderConvergesTo_zero_of_abs_le_gao
-- name    : OrderClosures.orderConvergesTo_zero_of_abs_le_gao
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:05:36.171004+00:00
-- url     : https://prove2.me/theorems/7d96f7e7-483b-4ca5-b8d6-6a1517495591
-- title:
--   Order Closures: order Converges To zero of abs le gao
-- statement:
--   Converts an absolute-value bound by an order-null net into order
--   convergence to zero; used in `solid_generated_orderAdherence`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/Iterations.lean#L644-L653
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/Iterations.lean#L644-L653

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

theorem OrderClosures.orderConvergesTo_zero_of_abs_le_gao
    {X : Type u} [AddCommGroup X] [Lattice X]
    {i : Type v} [Preorder i] {f g : i → X}
    (hg : OrderConvergesTo g 0) (hfg : ∀ j, |f j| ≤ |g j|) :
    OrderConvergesTo f 0 := by sorry

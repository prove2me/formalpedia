-- Prove2me | Theorems.Thm_OrderClosures_ordinalProjection_le_iff
-- name    : OrderClosures.ordinalProjection_le_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:00:03.720945+00:00
-- url     : https://prove2.me/theorems/dd93e174-b26f-460e-9d2c-90172e04d79b
-- title:
--   Order Closures: ordinal Projection le iff
-- statement:
--   Characterizes order between coordinate projections by CNF extension;
--   used in all dominator and strict-stage arguments.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/OrdinalSpace.lean#L168-L210
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/OrdinalSpace.lean#L168-L210

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_CNFOrder
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_OrdinalSpace
set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v

theorem OrderClosures.ordinalProjection_le_iff
    (ξ : Ordinal.{u}) (a b : GaoIndex ξ) :
    ordinalProjection ξ a ≤ ordinalProjection ξ b ↔ cnfExtensionLE a.1 b.1 := by sorry

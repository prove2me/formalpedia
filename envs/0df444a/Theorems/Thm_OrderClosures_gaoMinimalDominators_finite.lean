-- Prove2me | Theorems.Thm_OrderClosures_gaoMinimalDominators_finite
-- name    : OrderClosures.gaoMinimalDominators_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:02:52.836798+00:00
-- url     : https://prove2.me/theorems/379d9630-80f7-44bb-8118-c51d91a27a4a
-- title:
--   Order Closures: gao Minimal Dominators finite
-- statement:
--   Proves finiteness of the minimal dominator family; needed to combine it
--   with directedness of the positive approximating set.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/StageFormula.lean#L79-L94
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/StageFormula.lean#L79-L94

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_OrdinalSpace
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_StageFormula
set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v

theorem OrderClosures.gaoMinimalDominators_finite
    (ξ γ : Ordinal.{u}) {b : C(GaoCompactSpace ξ, ℝ)}
    (hb0 : 0 ≤ b) (hbne : b ≠ 0) :
    (gaoMinimalDominators ξ γ b).Finite := by sorry

-- Prove2me | Theorems.Thm_OrderClosures_gaoDominators_nonempty
-- name    : OrderClosures.gaoDominators_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:02:08.610812+00:00
-- url     : https://prove2.me/theorems/e1224355-c4ed-4cf0-9de0-f7eabd54db89
-- title:
--   Order Closures: gao Dominators nonempty
-- statement:
--   Extracts a coordinate projection dominating a positive Gao-stage element;
--   this starts the finite-minimal-dominator reduction.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/StageFormula.lean#L41-L47
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/StageFormula.lean#L41-L47

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_OrdinalSpace
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_StageFormula
set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v

theorem OrderClosures.gaoDominators_nonempty
    (ξ γ : Ordinal.{u}) {b : C(GaoCompactSpace ξ, ℝ)}
    (hb0 : 0 ≤ b) (hb : b ∈ GaoStageSet ξ γ) :
    (gaoDominators ξ γ b).Nonempty := by sorry

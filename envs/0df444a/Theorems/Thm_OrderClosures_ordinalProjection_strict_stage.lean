-- Prove2me | Theorems.Thm_OrderClosures_ordinalProjection_strict_stage
-- name    : OrderClosures.ordinalProjection_strict_stage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:03:41.340809+00:00
-- url     : https://prove2.me/theorems/3da25a47-e99e-419c-ab3d-0fe3f138a8ad
-- title:
--   Order Closures: ordinal Projection strict stage
-- statement:
--   The strict witness separating consecutive stages in Claim 3.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/StageFormula.lean#L653-L711
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/StageFormula.lean#L653-L711

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_OrdinalSpace
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_StageFormula
set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v

theorem OrderClosures.ordinalProjection_strict_stage
    (ξ γ : Ordinal.{u}) (hγ : γ ≤ ξ) :
    ∃ ζ : GaoIndex ξ,
      ordinalProjection ξ ζ ∈ GaoStageSet ξ (γ + 1) ∧
        ordinalProjection ξ ζ ∉ GaoStageSet ξ γ := by sorry

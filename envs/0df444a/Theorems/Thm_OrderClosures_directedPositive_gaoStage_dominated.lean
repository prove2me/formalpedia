-- Prove2me | Theorems.Thm_OrderClosures_directedPositive_gaoStage_dominated
-- name    : OrderClosures.directedPositive_gaoStage_dominated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:03:01.385617+00:00
-- url     : https://prove2.me/theorems/f2f71f05-d0d3-4594-95cd-44c4dbfad79d
-- title:
--   Order Closures: directed Positive gao Stage dominated
-- statement:
--   Produces one Gao-stage coordinate dominating an entire directed positive
--   family; this is the main input to the forward adherence inclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/StageFormula.lean#L98-L202
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/StageFormula.lean#L98-L202

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_OrdinalSpace
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_StageFormula
set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v

theorem OrderClosures.directedPositive_gaoStage_dominated
    (ξ γ : Ordinal.{u}) {z : C(GaoCompactSpace ξ, ℝ)}
    (hz : z ∈ directedPositiveAdherence (GaoStageSet ξ γ)) :
    ∃ α : GaoIndex ξ, α.1 ≤ Ordinal.omega0 ^ ξ ∧
      leastCNFExponent α.1 ≤ γ ∧ z ≤ ordinalProjection ξ α := by sorry
